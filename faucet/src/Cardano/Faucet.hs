{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}
{-# OPTIONS_GHC -Wall #-}
module Cardano.Faucet (
    FaucetAPI
  , faucetServer
  , faucetServerAPI
  , module Cardano.Faucet.Types
  , module Cardano.Faucet.Init
  ) where

import           Control.Lens
import           Control.Monad (forM_, unless)
import           Control.Monad.IO.Class (liftIO)
import           Data.ByteString.Lens (packedChars)
import           Data.Foldable (for_)
import           Data.Monoid ((<>))
import           Data.Tagged (retag)
import           Data.Text.Lazy (fromStrict)
import           Data.Text.Lazy.Lens (utf8)
import           Data.Text.Lens
import           Servant
import           System.Wlog (LoggerName (..), logError, logInfo, withSublogger)


import           Cardano.Wallet.API.V1.Types (Transaction (..), V1, unV1)
import           Pos.Core (Address (..))


import           Cardano.Faucet.Init
import           Cardano.Faucet.Metrics
import           Cardano.Faucet.Types
import           Cardano.Faucet.Types.Recaptcha
import qualified Cardano.WalletClient as Client

-- | Top level type of the faucet API
type FaucetAPI = "withdraw" :> Summary "Requests ADA from the faucet"
                            :> ReqBody '[FormUrlEncoded, JSON] WithdrawalRequest
                            :> Post '[JSON] WithdrawalResult
            :<|> "return-address" :> Summary "Get the address to return ADA to"
                                  :> Get '[JSON] (V1 Address)
            :<|> Raw
         -- :<|> "_deposit" :> ReqBody '[JSON] DepositRequest :> Post '[JSON] DepositResult

faucetServerAPI :: Proxy FaucetAPI
faucetServerAPI = Proxy

-- | Handler for the withdrawal of ADA from the faucet
withdraw :: (MonadFaucet c m) => WithdrawalRequest -> m WithdrawalResult
withdraw wr = withSublogger (LoggerName "withdraw") $ do
    logInfo "Attempting to send ADA"
    mCaptchaSecret <- view (feFaucetConfig . fcRecaptchaSecret)
    forM_ mCaptchaSecret $ \captchaSecret -> do
        let cr = CaptchaRequest captchaSecret (wr ^. gRecaptchaResponse)
        logInfo "Found a secret for recaptcha in config, attempting validation"
        captchaResp <- liftIO $ captchaRequest cr
        logInfo ("Recaptcha result: " <> (captchaResp ^. to show . packed))
        unless (captchaResp ^. success) $ do
            let captchaErrs = captchaResp ^. errorCodes . to show . packedChars
            throwError $ err400 { errBody = "Recaptcha had errors: " <> captchaErrs }
    resp <- Client.withdraw (wr ^. wAddress)
    case resp of
        Left _ -> do
            logError "Withdrawal queue is full"
            throwError $ err503 { errBody = "Withdrawal queue is full" }
        Right wdResp -> do
            for_ (wdResp ^? _WithdrawalSuccess) $ \txn -> do
              let amount = unV1 $ txAmount txn
              logInfo ((txn ^. to show . packed) <> " withdrew: "
                                                <> (amount ^. to show . packed))
              incWithDrawn amount
            for_ (wdResp  ^? _WithdrawalError) $ \err -> do
                logError ("Error from wallet: " <> err)
                throwError $ err503 { errBody = (fromStrict err) ^. re utf8 }
            return wdResp

-- | Get the address to return ADA to
returnAddress :: (MonadFaucet c m) => m (V1 Address)
returnAddress = view feReturnAddress

-- | Function to _deposit funds back into the faucet /not implemented/
_deposit :: (MonadFaucet c m) => DepositRequest -> m DepositResult
_deposit dr = withSublogger (LoggerName "_deposit") $ do
    -- decrWithDrawn (dr ^. dAmount)
    logInfo ((dr ^. to show . packed) <> " deposited")
    return DepositResult

-- | Serve the api, faucet form end point and a Raw endpoint for the html form
--
-- TODO: Get the server path from the config
faucetServer :: ServerT FaucetAPI M
faucetServer = withdraw :<|> returnAddress :<|> (retag $ serveDirectoryWebApp ".")

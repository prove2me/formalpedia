-- Prove2me | solution 1 for BitcoinSig.sigHashLegacy_anyoneCanPay
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:25:12.167808+00:00
-- url     : https://prove2.me/submissions/9b1861ee-ee8c-4b0a-aa18-08c496dbbadc

import Definitions.Def_BitcoinSig

namespace BS_8fbe
open BitcoinSig BitcoinSer

theorem BS_in (scriptCode : Bytes) (tx tx' : Tx) (nIn : Nat) (s n_ : Bool)
    (h4 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout)
    (h5 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence) :
    serSigInput tx' scriptCode nIn true s n_ = serSigInput tx scriptCode nIn true s n_ := by
  funext k
  simp only [serSigInput, if_true, h4, h5]

end BS_8fbe

open BitcoinSig BitcoinSer in
theorem solution (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat)
    (hacp : hashType &&& BitcoinSig.SIGHASH_ANYONECANPAY ≠ 0)
    (h1 : tx'.version = tx.version) (h2 : tx'.vout = tx.vout) (h3 : tx'.nLockTime = tx.nLockTime)
    (h4 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout)
    (h5 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence) :
    BitcoinSig.sigHashLegacy scriptCode tx' nIn hashType = BitcoinSig.sigHashLegacy scriptCode tx nIn hashType := by
  have hd : decide (hashType &&& SIGHASH_ANYONECANPAY ≠ 0) = true := decide_eq_true hacp
  have hs : serSigTx tx' scriptCode nIn hashType = serSigTx tx scriptCode nIn hashType := by
    simp only [serSigTx, hd, if_true, h1, h3, BS_8fbe.BS_in scriptCode tx tx' nIn _ _ h4 h5]
    unfold serSigOutput
    rw [h2]
  simp only [sigHashLegacy, hs, h2]

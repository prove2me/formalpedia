-- Prove2me | solution 1 for BitcoinSig.checkSig_empty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:25:19.957226+00:00
-- url     : https://prove2.me/submissions/121d10ee-59bd-41bc-8178-16113ab534f1

import Definitions.Def_BitcoinSig

open BitcoinSig BitcoinSer in
theorem solution (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion)
    (scriptCode pk : Bytes) (hpk : BitcoinSig.checkPubKeyEncoding f v pk = true) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount v scriptCode [] pk = some false := by
  simp [checkSigPreTapscript, checkSignatureEncoding, hpk, checkECDSASignature]

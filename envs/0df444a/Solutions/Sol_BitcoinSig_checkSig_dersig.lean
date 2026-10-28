-- Prove2me | solution 1 for BitcoinSig.checkSig_dersig
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:25:27.087772+00:00
-- url     : https://prove2.me/submissions/de43fdbd-babd-4126-a1e9-374bfdeec4f2

import Definitions.Def_BitcoinSig

open BitcoinSig BitcoinSer in
theorem solution (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion)
    (scriptCode sig pk : Bytes) (hf : f.dersig = true) (hne : sig ≠ [])
    (hder : BitcoinSig.isValidSignatureEncoding sig = false) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount v scriptCode sig pk = none := by
  have he : sig.isEmpty = false := by cases sig <;> simp_all
  simp [checkSigPreTapscript, checkSignatureEncoding, he, hf, hder]

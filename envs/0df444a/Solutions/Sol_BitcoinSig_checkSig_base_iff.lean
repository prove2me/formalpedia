-- Prove2me | solution 1 for BitcoinSig.checkSig_base_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:34:08.984285+00:00
-- url     : https://prove2.me/submissions/ab703952-c594-4508-a40a-9424d16a2c53

import Definitions.Def_BitcoinSig

open BitcoinSig BitcoinSer in
theorem solution (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int)
    (scriptCode sig pk : Bytes) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount .base scriptCode sig pk = some true ↔
      BitcoinSig.checkSignatureEncoding f sig = true ∧ BitcoinSig.checkPubKeyEncoding f .base pk = true ∧
      BitcoinSig.pubkeyValid pk = true ∧
      ∃ (sig' : Bytes) (ht : Byte), sig = sig' ++ [ht] ∧
        BitcoinSig.pubkeyVerify pk
          (BitcoinSig.sigHashLegacy (BitcoinSig.findAndDelete scriptCode (BitcoinSig.pushBytes sig)).1 tx nIn ht.toNat)
          sig' = true := by
  rcases List.eq_nil_or_concat sig with rfl | ⟨L, b, rfl⟩
  · simp [checkSigPreTapscript, checkECDSASignature]
  · simp only [checkSigPreTapscript, checkECDSASignature]
    by_cases h1 : checkSignatureEncoding f (L ++ [b]) = true <;>
    by_cases h2 : checkPubKeyEncoding f .base pk = true <;>
    by_cases h3 : pubkeyValid pk = true <;> simp [h1, h2, h3]
    constructor
    · intro h; exact ⟨L, b, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩; exact h

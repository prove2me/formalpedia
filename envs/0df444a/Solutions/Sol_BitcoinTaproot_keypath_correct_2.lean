-- Prove2me | solution 2 for BitcoinTaproot.keypath_correct
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:58:41.958324+00:00
-- url     : https://prove2.me/submissions/82c41882-c2d3-463f-b93c-e5fa610a7419

import Definitions.Def_BitcoinTaproot
import Theorems.Thm_BitcoinTaproot_checkSchnorr_iff
import Theorems.Thm_BitcoinTaproot_keypath_handler

open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

private theorem lexLt_asymm : ∀ (a b : Bytes), lexLt a b = true → lexLt b a = false
  | [], [], h => by simp [lexLt] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [lexLt] at h
  | x :: xs, y :: ys, h => by
    simp only [lexLt] at h ⊢
    by_cases h1 : x.toNat < y.toNat
    · rw [if_neg (by omega), if_pos h1]
    · rw [if_neg h1] at h
      by_cases h2 : y.toNat < x.toNat
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        rw [if_neg h2, if_neg h1]
        exact lexLt_asymm xs ys h

private theorem lexLt_total : ∀ (a b : Bytes), lexLt a b = false → lexLt b a = false → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [lexLt] at h
  | _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, h1, h2 => by
    simp only [lexLt] at h1 h2
    by_cases hxy : x.toNat < y.toNat
    · rw [if_pos hxy] at h1; cases h1
    · rw [if_neg hxy] at h1
      by_cases hyx : y.toNat < x.toNat
      · rw [if_pos hyx] at h2; cases h2
      · rw [if_neg hyx] at h1
        rw [if_neg hyx, if_neg hxy] at h2
        have hx : x = y := by
          have : x.toNat = y.toNat := by omega
          exact BitVec.eq_of_toNat_eq this
        rw [hx, lexLt_total xs ys h1 h2]

/-- **Taproot key-path spending is correct.** The output `OP_1 <q>` spent with the single witness
element `sig` verifies, under the Taproot flag, iff `sig` is a 64-byte BIP340 signature by `q` of the
BIP341 hash under `SIGHASH_DEFAULT`, or a 65-byte one under the non-zero hash type of its last byte. -/
theorem solution (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig q : Bytes) :
    BitcoinTaproot.taprootHandler spent c [sig] q = true ↔
      ∃ (body : Bytes) (ht : Nat) (h : Bytes), body.length = 64 ∧
        ((sig = body ∧ ht = 0) ∨ (∃ b : Byte, sig = body ++ [b] ∧ b.toNat = ht ∧ ht ≠ 0)) ∧
        BitcoinTaproot.sigHashSchnorr c.tx spent c.nIn ht false ⟨false, [], [], 0xFFFFFFFF⟩ = some h ∧
        BitcoinSig.schnorrVerify q h body = true := by
  rw [BitcoinTaproot.keypath_handler]
  exact BitcoinTaproot.checkSchnorr_iff _ _ _ _ _ _ _

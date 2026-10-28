-- Prove2me | solution 2 for BitcoinTaproot.sighash_type_invalid
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:58:13.245953+00:00
-- url     : https://prove2.me/submissions/f9f745ed-5f1d-4c6d-aaba-987d9ef84d06

import Definitions.Def_BitcoinTaproot

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

/-- Only hash types `0..3` and `0x81..0x83` are defined. -/
theorem solution (tx : Tx) (spent : List TxOut) (inPos hashType : Nat) (tapscript : Bool) (ed : ExecData)
    (h : ¬ (hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83))) :
    BitcoinTaproot.sigHashSchnorr tx spent inPos hashType tapscript ed = none := by
  unfold sigHashSchnorr; rw [if_pos h]

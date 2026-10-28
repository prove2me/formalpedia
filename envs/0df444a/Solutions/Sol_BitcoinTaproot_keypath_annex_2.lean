-- Prove2me | solution 2 for BitcoinTaproot.keypath_annex
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:58:15.285781+00:00
-- url     : https://prove2.me/submissions/04a1229f-ee24-4395-aaac-52514cb571a5

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

/-- With an annex, the key path commits to it: the handler is the Schnorr check with the annex hash. -/
theorem solution (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig annex q : Bytes)
    (ha : (annex.getD 0 0).toNat = BitcoinTaproot.ANNEX_TAG) (hne : annex ≠ []) :
    BitcoinTaproot.taprootHandler spent c [sig, annex] q =
      BitcoinTaproot.checkSchnorrSignature c.tx spent c.nIn sig q false
        ⟨true, BitcoinSer.sha256 (BitcoinSer.serBytes annex), [], 0xFFFFFFFF⟩ := by
  unfold taprootHandler
  have h2 : hasAnnex [sig, annex] = true := by
    unfold hasAnnex
    cases annex with
    | nil => exact absurd rfl hne
    | cons b _ => simp only [List.getD_cons_zero] at ha; simp [ha]
  simp [h2]

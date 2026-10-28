-- Prove2me | solution 1 for BitcoinTaproot.tapbranch_comm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:36:03.327043+00:00
-- url     : https://prove2.me/submissions/b3bded21-57b3-4619-9cc7-b3bf7b8d0316

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem S190TAP_lex_asymm : ∀ (a b : Bytes), lexLt a b = true → lexLt b a = false
  | [], [], h => by simp [lexLt] at h
  | [], _ :: _, _ => by simp [lexLt]
  | _ :: _, [], h => by simp [lexLt] at h
  | x :: xs, y :: ys, h => by
    simp only [lexLt] at h ⊢
    by_cases h1 : x.toNat < y.toNat
    · have : ¬ y.toNat < x.toNat := by omega
      simp [h1, this]
    · by_cases h2 : y.toNat < x.toNat
      · simp [h1, h2] at h
      · simp [h1, h2] at h ⊢
        exact S190TAP_lex_asymm xs ys h

theorem S190TAP_lex_total : ∀ (a b : Bytes), lexLt a b = false → lexLt b a = false → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [lexLt] at h
  | _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, h, h' => by
    simp only [lexLt] at h h'
    by_cases h1 : x.toNat < y.toNat
    · simp [h1] at h
    · by_cases h2 : y.toNat < x.toNat
      · simp [h2] at h'
      · simp [h1, h2] at h h'
        have hxy : x = y := by
          apply BitVec.eq_of_toNat_eq; omega
        rw [hxy, S190TAP_lex_total xs ys h h']

theorem solution (a b : Bytes) : BitcoinTaproot.tapbranchHash a b = BitcoinTaproot.tapbranchHash b a := by
  unfold tapbranchHash
  cases hab : lexLt a b
  · cases hba : lexLt b a
    · rw [S190TAP_lex_total a b hab hba]
    · rfl
  · rw [S190TAP_lex_asymm a b hab]; rfl

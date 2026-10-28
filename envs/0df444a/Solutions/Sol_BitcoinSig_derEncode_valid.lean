-- Prove2me | solution 1 for BitcoinSig.derEncode_valid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:34:11.719075+00:00
-- url     : https://prove2.me/submissions/c88e3333-0a8f-41bb-baf7-86e3fb0a66bb

import Definitions.Def_BitcoinSig

namespace BS_7b2f
open BitcoinSig BitcoinSer

theorem BS_gl (A B : Bytes) (n : Nat) (h : A.length ≤ n) :
    (A ++ B).getD n 0 = B.getD (n - A.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem BS_gr (A B : Bytes) (n : Nat) (h : n < A.length) :
    (A ++ B).getD n 0 = A.getD n 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem BS_c4 (a0 a1 a2 a3 : Byte) (L : Bytes) (i : Nat) :
    (a0 :: a1 :: a2 :: a3 :: L).getD (i + 4) 0 = L.getD i 0 := rfl

theorem BS_mid (r s : Bytes) (b0 b1 ht : Byte) (j : Nat) (hj : j < s.length) :
    (r ++ b0 :: b1 :: (s ++ [ht])).getD (r.length + 2 + j) 0 = s.getD j 0 := by
  rw [BS_gl _ _ _ (by omega), show r.length + 2 + j - r.length = j + 2 by omega]
  show (s ++ [ht]).getD j 0 = _
  rw [BS_gr _ _ _ hj]

theorem BS_tn (k : Nat) (h : k < 256) : (BitVec.ofNat 8 k).toNat = k := by
  simp [BitVec.toNat_ofNat]; omega

end BS_7b2f

open BitcoinSig BitcoinSer in
theorem solution (r s : Bytes) (ht : Byte) (hr : BitcoinSig.minimalInt r)
    (hs : BitcoinSig.minimalInt s) (hlen : r.length + s.length ≤ 66) :
    BitcoinSig.isValidSignatureEncoding (BitcoinSig.derEncode r s ht) = true := by
  obtain ⟨hr1, hr2, hr3⟩ := hr
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have lr : 0 < r.length := List.length_pos_iff.2 hr1
  have ls : 0 < s.length := List.length_pos_iff.2 hs1
  have e : derEncode r s ht = 0x30 :: BitVec.ofNat 8 (r.length + s.length + 4) :: 0x02 ::
      BitVec.ofNat 8 r.length :: (r ++ 0x02 :: BitVec.ofNat 8 s.length :: (s ++ [ht])) := by
    simp [derEncode]
  rw [e]
  generalize hE : (0x30 :: BitVec.ofNat 8 (r.length + s.length + 4) :: 0x02 ::
      BitVec.ofNat 8 r.length :: (r ++ 0x02 :: BitVec.ofNat 8 s.length :: (s ++ [ht])) : Bytes) = E
  have hl : E.length = r.length + s.length + 7 := by subst hE; simp; omega
  have f0 : (E.getD 0 0).toNat = 48 := by subst hE; rfl
  have f1 : (E.getD 1 0).toNat = r.length + s.length + 4 := by
    subst hE; exact BS_7b2f.BS_tn _ (by omega)
  have f2 : (E.getD 2 0).toNat = 2 := by subst hE; rfl
  have f3 : (E.getD 3 0).toNat = r.length := by subst hE; exact BS_7b2f.BS_tn _ (by omega)
  have f4 : (E.getD 4 0).toNat = (r.getD 0 0).toNat := by
    subst hE; rw [BS_7b2f.BS_c4 _ _ _ _ _ 0, BS_7b2f.BS_gr _ _ _ lr]
  have f5 : 1 < r.length → (E.getD 5 0).toNat = (r.getD 1 0).toNat := by
    intro h; subst hE; rw [BS_7b2f.BS_c4 _ _ _ _ _ 1, BS_7b2f.BS_gr _ _ _ h]
  have f6 : (E.getD (5 + r.length) 0).toNat = s.length := by
    subst hE; rw [show 5 + r.length = (r.length + 1) + 4 by omega, BS_7b2f.BS_c4,
      BS_7b2f.BS_gl _ _ _ (by omega), show r.length + 1 - r.length = 1 by omega]
    exact BS_7b2f.BS_tn _ (by omega)
  have f7 : (E.getD (r.length + 4) 0).toNat = 2 := by
    subst hE; rw [BS_7b2f.BS_c4, BS_7b2f.BS_gl _ _ _ (by omega), Nat.sub_self]; rfl
  have f8 : (E.getD (r.length + 6) 0).toNat = (s.getD 0 0).toNat := by
    subst hE; rw [show r.length + 6 = (r.length + 2 + 0) + 4 by omega, BS_7b2f.BS_c4,
      BS_7b2f.BS_mid _ _ _ _ _ _ ls]
  have f9 : 1 < s.length → (E.getD (r.length + 7) 0).toNat = (s.getD 1 0).toNat := by
    intro h
    subst hE; rw [show r.length + 7 = (r.length + 2 + 1) + 4 by omega, BS_7b2f.BS_c4,
      BS_7b2f.BS_mid _ _ _ _ _ _ h]
  have g5 : ¬ (1 < r.length ∧ (E.getD 4 0).toNat = 0 ∧ (E.getD 5 0).toNat < 0x80) := by
    rintro ⟨a, b, c⟩
    rw [f4] at b; rw [f5 a] at c
    have := hr3 a b; omega
  have g9 : ¬ (1 < s.length ∧ (E.getD (r.length + 6) 0).toNat = 0 ∧
      (E.getD (r.length + 7) 0).toNat < 0x80) := by
    rintro ⟨a, b, c⟩
    rw [f8] at b; rw [f9 a] at c
    have := hs3 a b; omega
  unfold isValidSignatureEncoding
  simp only [f3]
  rw [if_neg (show ¬ (E.length < 9) by omega)]
  rw [if_neg (show ¬ (73 < E.length) by omega)]
  rw [if_neg (show ¬ (BitVec.toNat (E.getD 0 0) ≠ 48) by omega)]
  rw [if_neg (show ¬ (BitVec.toNat (E.getD 1 0) ≠ E.length - 3) by omega)]
  rw [if_neg (show ¬ (E.length ≤ 5 + List.length r) by omega)]
  rw [if_neg (show ¬ (List.length r + BitVec.toNat (E.getD (5 + List.length r) 0) + 7 ≠ E.length) by omega)]
  rw [if_neg (show ¬ (BitVec.toNat (E.getD 2 0) ≠ 2) by omega)]
  rw [if_neg (show ¬ (List.length r = 0) by omega)]
  rw [if_neg (show ¬ (128 ≤ BitVec.toNat (E.getD 4 0)) by omega)]
  rw [if_neg (show ¬ (1 < List.length r ∧ BitVec.toNat (E.getD 4 0) = 0 ∧ BitVec.toNat (E.getD 5 0) < 128) by omega)]
  rw [if_neg (show ¬ (BitVec.toNat (E.getD (List.length r + 4) 0) ≠ 2) by omega)]
  rw [if_neg (show ¬ (BitVec.toNat (E.getD (5 + List.length r) 0) = 0) by omega)]
  rw [if_neg (show ¬ (128 ≤ BitVec.toNat (E.getD (List.length r + 6) 0)) by omega)]
  rw [if_neg (show ¬ (1 < BitVec.toNat (E.getD (5 + List.length r) 0) ∧ BitVec.toNat (E.getD (List.length r + 6) 0) = 0 ∧ BitVec.toNat (E.getD (List.length r + 7) 0) < 128) by omega)]

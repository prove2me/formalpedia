-- Prove2me | solution 1 for BitcoinSig.derEncode_complete
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:34:15.213549+00:00
-- url     : https://prove2.me/submissions/66b938f3-a7dd-4f0f-ac0e-7efd44e8e5c1

import Definitions.Def_BitcoinSig

namespace BS_a180
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

theorem BS_i4 (a0 a1 a2 a3 b0 b1 ht : Byte) (r s : Bytes) (h : 0 < r.length) :
    (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).getD 4 0 = r.getD 0 0 := by
  rw [BS_c4 _ _ _ _ _ 0, BS_gr _ _ _ h]

theorem BS_i5 (a0 a1 a2 a3 b0 b1 ht : Byte) (r s : Bytes) (h : 1 < r.length) :
    (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).getD 5 0 = r.getD 1 0 := by
  rw [BS_c4 _ _ _ _ _ 1, BS_gr _ _ _ h]

theorem BS_iR4 (a0 a1 a2 a3 b0 b1 ht : Byte) (r s : Bytes) :
    (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).getD (r.length + 4) 0 = b0 := by
  rw [BS_c4, BS_gl _ _ _ (by omega), Nat.sub_self]; rfl

theorem BS_iR5 (a0 a1 a2 a3 b0 b1 ht : Byte) (r s : Bytes) :
    (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).getD (5 + r.length) 0 = b1 := by
  rw [show 5 + r.length = (r.length + 1) + 4 by omega, BS_c4,
    BS_gl _ _ _ (by omega), show r.length + 1 - r.length = 1 by omega]; rfl

theorem BS_iR6 (a0 a1 a2 a3 b0 b1 ht : Byte) (r s : Bytes) (h : 0 < s.length) :
    (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).getD (r.length + 6) 0 = s.getD 0 0 := by
  rw [show r.length + 6 = (r.length + 2 + 0) + 4 by omega, BS_c4, BS_mid _ _ _ _ _ _ h]

theorem BS_iR7 (a0 a1 a2 a3 b0 b1 ht : Byte) (r s : Bytes) (h : 1 < s.length) :
    (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).getD (r.length + 7) 0 = s.getD 1 0 := by
  rw [show r.length + 7 = (r.length + 2 + 1) + 4 by omega, BS_c4, BS_mid _ _ _ _ _ _ h]

theorem BS_ite {c : Prop} [Decidable c] (X : Bool) :
    ((if c then false else X) = true) ↔ (¬ c ∧ X = true) := by
  by_cases h : c <;> simp [h]

theorem BS_struct (sig : Bytes) (lR lS : Nat) (hlen : sig.length = lR + lS + 7) :
    ∃ (a0 a1 a2 a3 : Byte) (r : Bytes) (b0 b1 : Byte) (s : Bytes) (ht : Byte),
      sig = a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht])) ∧
      r.length = lR ∧ s.length = lS := by
  match sig, hlen with
  | a0 :: a1 :: a2 :: a3 :: rest, hlen =>
    simp only [List.length_cons] at hlen
    have ht : (rest.drop lR).length = lS + 3 := by simp; omega
    match hd : rest.drop lR, ht with
    | b0 :: b1 :: u, ht =>
      simp only [List.length_cons] at ht
      have hw : (u.drop lS).length = 1 := by simp; omega
      obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 hw
      refine ⟨a0, a1, a2, a3, rest.take lR, b0, b1, u.take lS, c, ?_, by simp; omega,
        by simp; omega⟩
      have e1 : rest = rest.take lR ++ rest.drop lR := (List.take_append_drop _ _).symm
      have e2 : u = u.take lS ++ u.drop lS := (List.take_append_drop _ _).symm
      rw [hd, e2, hc] at e1
      rw [← e1]

end BS_a180

open BitcoinSig BitcoinSer in
theorem solution (sig : Bytes) (h : BitcoinSig.isValidSignatureEncoding sig = true) :
    ∃ (r s : Bytes) (ht : Byte), sig = BitcoinSig.derEncode r s ht ∧ BitcoinSig.minimalInt r ∧
      BitcoinSig.minimalInt s ∧ r.length + s.length ≤ 66 := by
  unfold isValidSignatureEncoding at h
  simp only [BS_a180.BS_ite] at h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, -⟩ := h
  obtain ⟨a0, a1, a2, a3, r, b0, b1, s, ht, rfl, hr, hs⟩ :=
    BS_a180.BS_struct sig (sig.getD 3 0).toNat (sig.getD (5 + (sig.getD 3 0).toNat) 0).toNat (by omega)
  have q3 : (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).getD 3 0 = a3 := rfl
  have q0 : (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).getD 0 0 = a0 := rfl
  have q1 : (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).getD 1 0 = a1 := rfl
  have q2 : (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).getD 2 0 = a2 := rfl
  have hL : (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [ht]))).length =
      r.length + s.length + 7 := by simp; omega
  simp only [q0, q1, q2, q3, hL] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 hr hs
  rw [← hr] at c5 c6 c8 c11 c12 c13 c14 hs
  rw [BS_a180.BS_iR5] at c6 c12 c14 hs
  rw [BS_a180.BS_iR4] at c11
  have lr : 0 < r.length := by omega
  have ls : 0 < s.length := by omega
  rw [BS_a180.BS_i4 _ _ _ _ _ _ _ _ _ lr] at c9 c10
  rw [BS_a180.BS_iR6 _ _ _ _ _ _ _ _ _ ls] at c13 c14
  have e0 : a0 = 0x30 := BitVec.eq_of_toNat_eq (by simp; omega)
  have e1 : a1 = BitVec.ofNat 8 (r.length + s.length + 4) :=
    BitVec.eq_of_toNat_eq (by rw [BS_a180.BS_tn _ (by omega)]; omega)
  have e2 : a2 = 0x02 := BitVec.eq_of_toNat_eq (by simp; omega)
  have e3 : a3 = BitVec.ofNat 8 r.length :=
    BitVec.eq_of_toNat_eq (by rw [BS_a180.BS_tn _ (by omega)]; omega)
  have e4 : b0 = 0x02 := BitVec.eq_of_toNat_eq (by simp; omega)
  have e5 : b1 = BitVec.ofNat 8 s.length :=
    BitVec.eq_of_toNat_eq (by rw [BS_a180.BS_tn _ (by omega)]; omega)
  refine ⟨r, s, ht, ?_, ⟨List.ne_nil_of_length_pos lr, by omega, ?_⟩,
    ⟨List.ne_nil_of_length_pos ls, by omega, ?_⟩, by omega⟩
  · subst e0 e1 e2 e3 e4 e5; simp [derEncode]
  · intro h1 h2
    rw [BS_a180.BS_i5 _ _ _ _ _ _ _ _ _ h1] at c10
    omega
  · intro h1 h2
    rw [BS_a180.BS_iR7 _ _ _ _ _ _ _ _ _ h1] at c14
    omega

-- Prove2me | solution 1 for DiazModulus.matrix_exists_rank_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:27:16.073306+00:00
-- url     : https://prove2.me/submissions/ef80ac56-724a-4d1d-b536-eb29d4346d17

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Rank normal form of a matrix over a field

For an `s × t` matrix `N` over a field `k` we find invertible `P`, `Q` with `PNQ = (I_r 0; 0 0)`, by strong
induction on `s`. If `N = 0`, take `r = 0` and `P = Q = 1`. Otherwise swap rows `0, a` and columns `0, b` to
bring a non-zero entry `N_ab` to the corner, and write the result in blocks `(A B; C D)` with `A = (N_ab)`
invertible. Row and column elimination give
`(A⁻¹ 0; 0 P')(1 0; −CA⁻¹ 1)(A B; C D)(1 −A⁻¹B; 0 1)(1 0; 0 Q') = (1 0; 0 P'SQ')`, where `S = D − CA⁻¹B` is the
Schur complement and `P'`, `Q'` put `S` (with one row fewer) in normal form of rank `r'` by the induction
hypothesis. Then `r = r' + 1`; the transforming matrices are block triangular with unit determinants, and
composing them with the two swaps keeps their determinants units. -/

open DiazModulus in
theorem solution {k : Type*} [Field k] {s t : ℕ}
    (N : Matrix (Fin s) (Fin t) k) :
    ∃ (r : ℕ) (P : Matrix (Fin s) (Fin s) k) (Q : Matrix (Fin t) (Fin t) k),
      r ≤ s ∧ r ≤ t ∧ IsUnit P.det ∧ IsUnit Q.det ∧
      ∀ (i : Fin s) (j : Fin t), (P * N * Q) i j = if i.val = j.val ∧ i.val < r then 1 else 0 := by
  classical
  induction s using Nat.strong_induction_on generalizing t with
  | _ s ih =>
  by_cases hN : N = 0
  · exact ⟨0, 1, 1, Nat.zero_le _, Nat.zero_le _, by simp, by simp, fun i j => by simp [hN]⟩
  obtain ⟨a, b, hab⟩ : ∃ a b, N a b ≠ 0 := by
    by_contra h; exact hN (Matrix.ext fun i j => not_not.1 fun h' => h ⟨i, j, h'⟩)
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ s from Fin.pos a)
  obtain ⟨t', rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ t from Fin.pos b)
  let es : Fin 1 ⊕ Fin s' ≃ Fin (1 + s') := finSumFinEquiv
  let et : Fin 1 ⊕ Fin t' ≃ Fin (1 + t') := finSumFinEquiv
  let gs : Fin (1 + s') ≃ Fin 1 ⊕ Fin s' := (Equiv.swap 0 a).trans es.symm
  let gt : Fin (1 + t') ≃ Fin 1 ⊕ Fin t' := (Equiv.swap 0 b).trans et.symm
  let N2 := N.submatrix gs.symm gt.symm
  have hN2 : N = N2.submatrix gs gt := by simp [N2]
  set A := N2.toBlocks₁₁ with hAdef
  have hA : IsUnit A.det := by
    have h0s : (Fin.castAdd s' (0 : Fin 1) : Fin (1 + s')) = 0 := Fin.ext (by simp)
    have h0t : (Fin.castAdd t' (0 : Fin 1) : Fin (1 + t')) = 0 := Fin.ext (by simp)
    rw [Matrix.det_unique, isUnit_iff_ne_zero]
    simpa [A, N2, gs, gt, es, et, Matrix.toBlocks₁₁, h0s, h0t] using hab
  let _ := Matrix.invertibleOfIsUnitDet A hA
  set S := N2.toBlocks₂₂ - N2.toBlocks₂₁ * ⅟A * N2.toBlocks₁₂ with hSdef
  obtain ⟨r', P', Q', hr's, hr't, hP', hQ', hS⟩ := ih s' (by omega) S
  let P2 := Matrix.fromBlocks (⅟A) 0 0 P' * Matrix.fromBlocks 1 0 (-(N2.toBlocks₂₁ * ⅟A)) 1
  let Q2 := Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) k) (-(⅟A * N2.toBlocks₁₂)) 0 1 *
    Matrix.fromBlocks 1 0 0 Q'
  have key : P2 * N2 * Q2 = Matrix.fromBlocks 1 0 0 (P' * S * Q') := by
    rw [← Matrix.fromBlocks_toBlocks N2]
    simp only [P2, Q2, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
    congr 1
    · exact invOf_mul_self _
    · simp only [← hAdef, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.mul_invOf_cancel_left,
        neg_add_cancel]
    · simp only [← hAdef, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one,
        neg_add_cancel]
    · simp only [← hAdef, hSdef, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, invOf_mul_self,
        Matrix.mul_one, neg_add_cancel, Matrix.zero_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul]
      abel
  have hP2 : IsUnit P2.det := by
    simp only [P2, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_one, mul_one]
    exact (Matrix.isUnit_det_of_left_inverse (mul_invOf_self A)).mul hP'
  have hQ2 : IsUnit Q2.det := by
    simp only [Q2, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    exact hQ'
  refine ⟨r' + 1, P2.submatrix es.symm gs, Q2.submatrix gt et.symm, by omega, by omega, ?_, ?_, ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := P2⁻¹.submatrix gs es.symm) ?_
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hP2, Matrix.submatrix_one_equiv]
  · refine Matrix.isUnit_det_of_right_inverse (B := Q2⁻¹.submatrix et.symm gt) ?_
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hQ2, Matrix.submatrix_one_equiv]
  · intro i j
    have e1 : P2.submatrix es.symm gs * N * Q2.submatrix gt et.symm =
        (Matrix.fromBlocks 1 0 0 (P' * S * Q')).submatrix es.symm et.symm := by
      rw [hN2, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, key]
    rw [e1, Matrix.submatrix_apply]
    obtain ⟨u, rfl⟩ := es.surjective i
    obtain ⟨v, rfl⟩ := et.surjective j
    rcases u with u | u <;> rcases v with v | v <;>
      simp [es, et, hS, Fin.fin_one_eq_zero] <;>
      first | omega | (split_ifs <;> first | rfl | (exfalso; omega))

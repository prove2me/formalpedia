-- Prove2me | solution 1 for D1Bound5.full_ring_productFour_mixed_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:56:54.86616+00:00
-- url     : https://prove2.me/submissions/e3a4225d-6616-436a-a9d7-4ff1016f9a54

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_MixedProductFourGrowth_Definitions
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_exists_mixed_symmetric_root_matrix_with_roots
import Theorems.Thm_D1Bound5_full_ring_scaledRootMatrix_det_norm_lower
import Theorems.Thm_D1Bound5_mixed_four_det_ne_zero_of_entry_bounds
import Theorems.Thm_D1Bound5_mixed_signed_root_det_and_adjugate_upper
import Theorems.Thm_D1Bound5_normalizedRootError_diag
import Theorems.Thm_D1Bound5_productFour_mixed_growth_from_bounds
import Theorems.Thm_D1Bound5_productFour_ordered_square_sum
import Theorems.Thm_D1Bound5_productFour_tail_large

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5













/-- The mixed A >= 1, B >= 3 growth estimate in every imaginary quadratic
full integer ring. The original-ring square roots and sign choices are
constructed without excluding zero squares or equal complex moduli. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (M : Matrix (Fin 4) (Fin 4) (𝓞 K))
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : 1 ≤ ‖phi (a 0 : K)‖)
    (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (htail : 2 * ‖phi (a 1 : K)‖ * ‖phi (a 2 : K)‖ <
      ‖phi (a 3 : K)‖) :
    (3/2 : ℝ)*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*
      ‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A : ℝ := ‖phi (a 0 : K)‖
  let B : ℝ := ‖phi (a 1 : K)‖
  let C : ℝ := ‖phi (a 2 : K)‖
  let D : ℝ := ‖phi (a 3 : K)‖
  have hAB : A ≤ B := hmon (by decide : (0 : Fin 4) ≤ 1)
  have hBC : B ≤ C := hmon (by decide : (1 : Fin 4) ≤ 2)
  have hD18 : 18 < D := productFour_tail_large B C D hBC hB htail
  have hAl : 0 ≤ A := norm_nonneg _
  have hAall (i : Fin 4) : 1 ≤ ‖f (a i)‖ := by
    change 1 ≤ ‖phi (a i : K)‖
    exact hA.trans (hmon (Fin.zero_le i))
  have hBall (i : Fin 4) (hi : i ≠ 0) : 3 ≤ ‖f (a i)‖ := by
    change 3 ≤ ‖phi (a i : K)‖
    have hOne : (1 : Fin 4) ≤ i := by omega
    exact hB.trans (hmon hOne)
  have hfirst (i j : Fin 4) (hij : i ≠ j)
      (hz : i = 0 ∨ j = 0) : 3 ≤ ‖f (a i) * f (a j)‖ := by
    rw [norm_mul]
    rcases hz with hi | hj
    · subst i
      have hji : j ≠ 0 := hij.symm
      have h1 := hAall 0
      have h3 := hBall j hji
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h3)]
    · subst j
      have h1 := hAall 0
      have h3 := hBall i hij
      nlinarith [mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h1)]
  have hlater (i j : Fin 4) (_ : i ≠ j)
      (hz : ¬(i = 0 ∨ j = 0)) : 9 ≤ ‖f (a i) * f (a j)‖ := by
    have hi : i ≠ 0 := by tauto
    have hj : j ≠ 0 := by tauto
    have h1 := hBall i hi
    have h2 := hBall j hj
    rw [norm_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  obtain ⟨u, S, hu, hd, hs, _, hsq, hgood⟩ :=
    exists_mixed_symmetric_root_matrix_with_roots f a M
      hdiag hsymm hroot hfirst hlater
  let w : Fin 4 → ℂ := fun i => f (a i)
  let F := normalizedRootError w u (S.map f)
  have hFdiag : ∀ i, F i i = 0 := by
    intro i
    exact normalizedRootError_diag w u (S.map f) (by simpa [w] using hu)
      (fun j => congrArg f (hd j)) i
  have hFfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖F i j - (1/2 : ℂ)‖ < (1/18 : ℝ) := by
    intro i j hij hz
    have h : SignedEntryBounds f (a i) (a j) (u i) (u j)
        (S i j) (5/9) (25/486) := by
      simpa [MixedSignedEntryGood, hz] using hgood i j hij
    change ‖(u i * f (S i j) * u j - f (a i) * f (a j)) -
      (1/2 : ℂ)‖ < (1/18 : ℝ)
    exact lt_trans h.2 (by norm_num)
  have hFlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖F i j - (1/2 : ℂ)‖ < (1/64 : ℝ) := by
    intro i j hij hz
    have h : SignedEntryBounds f (a i) (a j) (u i) (u j)
        (S i j) (7/13) (1/64) := by
      simpa [MixedSignedEntryGood, hz] using hgood i j hij
    change ‖(u i * f (S i j) * u j - f (a i) * f (a j)) -
      (1/2 : ℂ)‖ < (1/64 : ℝ)
    exact h.2
  have hF : F.det ≠ 0 :=
    mixed_four_det_ne_zero_of_entry_bounds F hFdiag hFfirst hFlater
  have hmap : S.map f = (fun i j => f (S i j)) := by
    ext i j
    rfl
  have hanalytic : ‖F.det‖ < (3/10 : ℝ) ∧
      ‖F.adjugate‖ < (155/96 : ℝ)*(59/96)^2 := by
    simpa only [F, w, hmap] using
      mixed_signed_root_det_and_adjugate_upper f a u S hu hd hs hgood
  have hdetNumeric : (3/10 : ℝ) <
      productFourMixedH * productFourMixedS^3 := by
    unfold productFourMixedH productFourMixedS
    norm_num
  have hdet : ‖F.det‖ < productFourMixedH * productFourMixedS^3 :=
    lt_trans hanalytic.1 hdetNumeric
  have hadj : ‖F.adjugate‖ < productFourMixedH * productFourMixedS^2 := by
    simpa [productFourMixedH, productFourMixedS] using hanalytic.2
  have hsum := productFour_ordered_square_sum A B C D hAl hAB hBC hB htail
  have hw : (∑ i, ‖w i‖^2) ≤ (13/12 : ℝ) * D^2 := by
    simpa [w, f, A, B, C, D, Fin.sum_univ_four] using hsum
  have hlower := full_ring_scaledRootMatrix_det_norm_lower hK phi
    (by decide : Even (Fintype.card (Fin 4))) a S hd hsq u hu
  have hmatrix : F + Matrix.vecMulVec w w = scaledRootMatrix u (S.map f) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply,
      F, w, normalizedRootError, scaledRootMatrix, Matrix.map_apply]
    ring
  have hlower' : A*B*C*D ≤ ‖(F + Matrix.vecMulVec w w).det‖ := by
    rw [hmatrix]
    convert hlower using 1
    simp [A, B, C, D, Fin.prod_univ_four]
  exact productFour_mixed_growth_from_bounds F w A B C D hD18
    hF hdet hadj hw hlower'



end D1Bound5
end

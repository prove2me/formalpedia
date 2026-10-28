-- Prove2me | solution 1 for D1Bound5.full_ring_productFour_large_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:38:15.713995+00:00
-- url     : https://prove2.me/submissions/c8ffe648-418a-4b5b-99f3-95e8a82b1ae7

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
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
import Mathlib.Data.Int.GCD
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_exists_good_symmetric_root_matrix_with_roots
import Theorems.Thm_D1Bound5_full_ring_scaledRootMatrix_det_norm_lower
import Theorems.Thm_D1Bound5_productFour_growth_from_bounds
import Theorems.Thm_D1Bound5_productFour_ordered_square_sum
import Theorems.Thm_D1Bound5_productFour_tail_large
import Theorems.Thm_D1Bound5_reference_perturbed_det_ne_zero_of_near
import Theorems.Thm_D1Bound5_signed_root_matrix_adjugate_upper
import Theorems.Thm_D1Bound5_signed_root_matrix_det_upper
import Theorems.Thm_D1Bound5_signed_root_matrix_operator_bound

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5





end D1Bound5

namespace D1Bound5

/-- The A >= 3 part of the four-entry determinant growth lemma, for every
imaginary quadratic FULL integer ring. The tail-growth assumption is the
separately proved irregular-tail lemma, not a replacement for the result. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (M : Matrix (Fin 4) (Fin 4) (𝓞 K))
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : 3 ≤ ‖phi (a 0 : K)‖)
    (htail : 2 * ‖phi (a 1 : K)‖ * ‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖) :
    2 * ‖phi (a 0 : K)‖ * ‖phi (a 1 : K)‖ * ‖phi (a 2 : K)‖ <
      ‖phi (a 3 : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A : ℝ := ‖phi (a 0 : K)‖
  let B : ℝ := ‖phi (a 1 : K)‖
  let C : ℝ := ‖phi (a 2 : K)‖
  let D : ℝ := ‖phi (a 3 : K)‖
  have hAB : A ≤ B := hmon (by decide : (0 : Fin 4) ≤ 1)
  have hBC : B ≤ C := hmon (by decide : (1 : Fin 4) ≤ 2)
  have hAC : C ≤ D := hmon (by decide : (2 : Fin 4) ≤ 3)
  have hAl : 0 ≤ A := norm_nonneg _
  have hB3 : 3 ≤ B := le_trans hA hAB
  have hD18 : 18 < D := productFour_tail_large B C D hBC hB3 htail
  have hlarge (i j : Fin 4) (_ : i ≠ j) :
      9 ≤ ‖f (a i) * f (a j)‖ := by
    have hi : 3 ≤ ‖f (a i)‖ := by
      change 3 ≤ ‖phi (a i : K)‖
      exact hA.trans (hmon (Fin.zero_le i))
    have hj : 3 ≤ ‖f (a j)‖ := by
      change 3 ≤ ‖phi (a j : K)‖
      exact hA.trans (hmon (Fin.zero_le j))
    rw [norm_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr hj)]
  obtain ⟨u, S, hu, hd, hs, _, hsq, hgood⟩ :=
    exists_good_symmetric_root_matrix_with_roots f a M
      hdiag hsymm hroot hlarge
  let w : Fin 4 → ℂ := fun i => f (a i)
  let F := normalizedRootError w u (S.map f)
  have hnear : ‖F - halfOffDiagonal‖ < 3 * (128/8649 : ℝ) :=
    signed_root_matrix_operator_bound f a u S hu hd hgood
  have hF : F.det ≠ 0 := reference_perturbed_det_ne_zero_of_near F hnear
  have hdet : ‖F.det‖ < productFourH * productFourS^3 :=
    signed_root_matrix_det_upper f a u S hu hd hs hgood
  have hadj : ‖F.adjugate‖ < productFourH * productFourS^2 :=
    signed_root_matrix_adjugate_upper f a u S hu hd hs hgood
  have hsum := productFour_ordered_square_sum A B C D hAl hAB hBC hB3 htail
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
  exact productFour_growth_from_bounds F w A B C D hD18 hF hdet hadj hw hlower'

end D1Bound5
end

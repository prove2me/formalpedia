-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.frontier_large_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:13:04.020521+00:00
-- url     : https://prove2.me/submissions/c74f84e0-dcc5-44a8-9f54-afffbd423eac

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_exists_symmetric_root_matrix
import Theorems.Thm_D1Bound5_IsD1Tuple_productFour_large_growth
import Theorems.Thm_D1Bound5_exists_good_symmetric_root_matrix_with_roots
import Theorems.Thm_D1Bound5_frontier_large_adjugate_entry_bounds
import Theorems.Thm_D1Bound5_frontier_large_rankOne_det_bound
import Theorems.Thm_D1Bound5_full_ring_scaledRootMatrix_det_norm_lower
import Theorems.Thm_D1Bound5_normalizedRootError_diag
import Theorems.Thm_D1Bound5_reference_perturbed_det_ne_zero_of_near
import Theorems.Thm_D1Bound5_signed_root_matrix_det_upper
import Theorems.Thm_D1Bound5_signed_root_matrix_operator_bound

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5

/-- The sharpened FOUR-entry frontier gap: an ordered D(1)-quadruple
whose smallest modulus is at least three has T>3ABS. It follows from
the proved product-four constant two and a more precise entrywise use
of the already-established adjugate estimates. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : 3 ≤ ‖phi (a 0 : K)‖) :
    3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ <
      ‖phi (a 3 : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let w : Fin 4 → ℂ := fun i => f (a i)
  let A := ‖w 0‖
  let B := ‖w 1‖
  let C := ‖w 2‖
  let D := ‖w 3‖
  have hB : 3 ≤ B := hA.trans (hmon (by decide : (0 : Fin 4) ≤ 1))
  have hC : 3 ≤ C := hB.trans (hmon (by decide : (1 : Fin 4) ≤ 2))
  change 3 ≤ A at hA
  have hAB : 9 ≤ A*B := by
    nlinarith only [hA, hB, mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hfirst : 2*A*B*C < D :=
    IsD1Tuple.productFour_large_growth hK phi a ha hmon hA
  have h18 : 18*C < D := by
    nlinarith only [hfirst, mul_nonneg (sub_nonneg.mpr hAB) (show 0 ≤ C by linarith)]
  have hD : 54 ≤ D := by linarith only [h18, hC]
  have hw (i : Fin 4) (hi : i ≠ 3) : ‖w i‖ ≤ D/18 := by
    have hsmall : ‖w i‖ ≤ C := hmon (by omega : i ≤ 2)
    linarith only [hsmall, h18]
  obtain ⟨M, hdiag, hsym, hroot⟩ := ha.exists_symmetric_root_matrix a
  have hlarge (i j : Fin 4) (_ : i ≠ j) : 9 ≤ ‖f (a i)*f (a j)‖ := by
    have hi : 3 ≤ ‖f (a i)‖ := hA.trans (hmon (Fin.zero_le i))
    have hj : 3 ≤ ‖f (a j)‖ := hA.trans (hmon (Fin.zero_le j))
    rw [norm_mul]
    nlinarith only [hi, hj, mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr hj)]
  obtain ⟨u,S,hu,hd,hs,_,hsq,hgood⟩ :=
    exists_good_symmetric_root_matrix_with_roots f a M hdiag hsym hroot hlarge
  let F := normalizedRootError w u (S.map f)
  have hzero (i : Fin 4) : F i i = 0 :=
    normalizedRootError_diag w u (S.map f) hu (fun j => congrArg f (hd j)) i
  have hsymF (i j : Fin 4) : F i j = F j i := by
    change u i*f (S i j)*u j-f (a i)*f (a j) =
      u j*f (S j i)*u i-f (a j)*f (a i)
    rw [hs i j]
    ring
  have hnear (i j : Fin 4) (hij : i ≠ j) :
      ‖F i j-(1/2 : ℂ)‖ < (128/8649 : ℝ) := (hgood i j hij).2
  have hG := frontier_large_adjugate_entry_bounds F hzero hsymF hnear
  have hFnear : ‖F-halfOffDiagonal‖ < 3*(128/8649 : ℝ) :=
    signed_root_matrix_operator_bound f a u S hu hd hgood
  have hF : F.det ≠ 0 := reference_perturbed_det_ne_zero_of_near F hFnear
  have hdet : ‖F.det‖ < (1/4 : ℝ) :=
    (signed_root_matrix_det_upper f a u S hu hd hs hgood).trans
      (by unfold productFourH productFourS; norm_num)
  have hupper := frontier_large_rankOne_det_bound F w D hD hF hdet hG hw rfl
  have hmatrix : F+Matrix.vecMulVec w w = scaledRootMatrix u (S.map f) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply,
      F, w, normalizedRootError, scaledRootMatrix, Matrix.map_apply]
    ring
  have hlower := full_ring_scaledRootMatrix_det_norm_lower hK phi
    (by decide : Even (Fintype.card (Fin 4))) a S hd hsq u hu
  have hlower' : A*B*C*D ≤ ‖(F+Matrix.vecMulVec w w).det‖ := by
    rw [hmatrix]
    convert hlower using 1
    simp [A, B, C, D, w, f, Fin.prod_univ_four]
  have hmul : (3*A*B*C)*D < D*D := by nlinarith only [hlower', hupper]
  change 3*A*B*C < D
  by_contra hn
  have hnonneg := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn))
    (show 0 ≤ D by linarith only [hD])
  nlinarith only [hmul, hnonneg]

end D1Bound5
end

-- Prove2me | solution 1 for D1Bound5.productFour_rankOne_numeric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:27.109665+00:00
-- url     : https://prove2.me/submissions/46d94796-9400-4eb8-a93e-b4bc21ddecf3

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
import Theorems.Thm_D1Bound5_rankOneDeterminant_adjugate_norm_le

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5







/-- The rank-one determinant bound reduces the large-entry branch to
the two still-open perturbative determinant and adjugate estimates.
These estimates are assumptions here, not asserted as established. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ)
    (D : ℝ) (hD : 18 < D)
    (hF : F.det ≠ 0)
    (hdet : ‖F.det‖ < productFourH * productFourS^3)
    (hadj : ‖F.adjugate‖ < productFourH * productFourS^2)
    (hw : (∑ i, ‖w i‖^2) ≤ (13/12 : ℝ) * D^2) :
    ‖(F + Matrix.vecMulVec w w).det‖ < D^2 / 2 := by
  have hsum : 0 ≤ (∑ i, ‖w i‖^2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcoef : 0 ≤ productFourH * productFourS^2 := by
    unfold productFourH productFourS
    positivity
  have hterm :
      ‖F.adjugate‖ * (∑ i, ‖w i‖^2) ≤
        productFourH * productFourS^2 * ((13/12 : ℝ) * D^2) := by
    calc
      _ ≤ (productFourH * productFourS^2) * (∑ i, ‖w i‖^2) :=
        mul_le_mul_of_nonneg_right hadj.le hsum
      _ ≤ productFourH * productFourS^2 * ((13/12 : ℝ) * D^2) :=
        mul_le_mul_of_nonneg_left hw hcoef
  have hn :
      productFourH * productFourS^3 +
        productFourH * productFourS^2 * ((13/12 : ℝ) * D^2) < D^2/2 := by
    have hd2 : 324 < D^2 := by nlinarith
    unfold productFourH productFourS
    nlinarith only [hd2]
  have hbase := rankOneDeterminant_adjugate_norm_le F w hF
  linarith only [hbase, hdet, hterm, hn]



end D1Bound5
end

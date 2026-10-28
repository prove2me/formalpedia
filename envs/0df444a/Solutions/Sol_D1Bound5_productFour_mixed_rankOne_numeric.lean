-- Prove2me | solution 1 for D1Bound5.productFour_mixed_rankOne_numeric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:39.435489+00:00
-- url     : https://prove2.me/submissions/297c72f8-868d-49b5-9bee-7d1196b25f7e

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
import Definitions.Def_D1Bound5_MixedProductFourGrowth_Definitions
import Theorems.Thm_D1Bound5_rankOneDeterminant_adjugate_norm_le

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5








/-- The mixed rank-one determinant inequality. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ)
    (D : ℝ) (hD : 18 < D) (hF : F.det ≠ 0)
    (hdet : ‖F.det‖ < productFourMixedH * productFourMixedS^3)
    (hadj : ‖F.adjugate‖ < productFourMixedH * productFourMixedS^2)
    (hw : (∑ i, ‖w i‖^2) ≤ (13/12 : ℝ) * D^2) :
    ‖(F + Matrix.vecMulVec w w).det‖ < (2/3 : ℝ)*D^2 := by
  have hsum : 0 ≤ (∑ i, ‖w i‖^2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcoef : 0 ≤ productFourMixedH * productFourMixedS^2 := by
    unfold productFourMixedH productFourMixedS
    positivity
  have hterm :
      ‖F.adjugate‖ * (∑ i, ‖w i‖^2) ≤
        productFourMixedH * productFourMixedS^2 * ((13/12 : ℝ) * D^2) := by
    calc
      _ ≤ (productFourMixedH * productFourMixedS^2) * (∑ i, ‖w i‖^2) :=
        mul_le_mul_of_nonneg_right hadj.le hsum
      _ ≤ productFourMixedH * productFourMixedS^2 * ((13/12 : ℝ) * D^2) :=
        mul_le_mul_of_nonneg_left hw hcoef
  have hn :
      productFourMixedH * productFourMixedS^3 +
        productFourMixedH * productFourMixedS^2 * ((13/12 : ℝ) * D^2) <
        (2/3 : ℝ)*D^2 := by
    have hd2 : 324 < D^2 := by nlinarith
    unfold productFourMixedH productFourMixedS
    nlinarith only [hd2]
  have hbase := rankOneDeterminant_adjugate_norm_le F w hF
  linarith only [hbase, hdet, hterm, hn]








end D1Bound5
end

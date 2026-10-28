-- Prove2me | solution 1 for D1Bound5.productFour_mixed_growth_from_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:01:16.936283+00:00
-- url     : https://prove2.me/submissions/7975db4b-4876-4b41-b009-a1d80cc322f8

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
import Theorems.Thm_D1Bound5_productFour_mixed_rankOne_numeric

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5










/-- D > 3ABC/2 from the mixed determinant bounds and the arithmetic lower bound. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ)
    (A B C D : ℝ) (hD : 18 < D) (hF : F.det ≠ 0)
    (hdet : ‖F.det‖ < productFourMixedH * productFourMixedS^3)
    (hadj : ‖F.adjugate‖ < productFourMixedH * productFourMixedS^2)
    (hw : (∑ i, ‖w i‖^2) ≤ (13/12 : ℝ) * D^2)
    (hlower : A*B*C*D ≤ ‖(F + Matrix.vecMulVec w w).det‖) :
    (3/2 : ℝ)*A*B*C < D := by
  have ht := productFour_mixed_rankOne_numeric F w D hD hF hdet hadj hw
  have hDpos : 0 < D := by linarith
  have hprod : ((3/2 : ℝ)*A*B*C)*D < D*D := by
    nlinarith only [hlower, ht]
  by_contra hbad
  have hmul := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hbad)) hDpos.le
  nlinarith only [hprod, hmul]






end D1Bound5
end

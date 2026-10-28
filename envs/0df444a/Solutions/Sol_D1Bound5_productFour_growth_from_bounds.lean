-- Prove2me | solution 1 for D1Bound5.productFour_growth_from_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:46:48.215002+00:00
-- url     : https://prove2.me/submissions/20e478ba-d126-48b3-8f6b-211a19adeb2c

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
import Theorems.Thm_D1Bound5_productFour_rankOne_numeric

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5









/-- The final numerical implication D > 2ABC, conditional on the
integral determinant lower bound and the perturbative estimates. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ)
    (A B C D : ℝ) (hD : 18 < D)
    (hF : F.det ≠ 0)
    (hdet : ‖F.det‖ < productFourH * productFourS^3)
    (hadj : ‖F.adjugate‖ < productFourH * productFourS^2)
    (hw : (∑ i, ‖w i‖^2) ≤ (13/12 : ℝ) * D^2)
    (hlower : A*B*C*D ≤ ‖(F + Matrix.vecMulVec w w).det‖) :
    2*A*B*C < D := by
  have ht := productFour_rankOne_numeric F w D hD hF hdet hadj hw
  have hDpos : 0 < D := by linarith
  have hprod : (2*A*B*C)*D < D*D := by
    nlinarith only [hlower, ht]
  have hg : 2*A*B*C < D := by
    by_contra hbad
    have hmul := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hbad)) hDpos.le
    nlinarith only [hprod, hmul]
  exact hg

end D1Bound5
end

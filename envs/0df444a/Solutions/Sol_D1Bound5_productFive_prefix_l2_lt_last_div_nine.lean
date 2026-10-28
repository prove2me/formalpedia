-- Prove2me | solution 1 for D1Bound5.productFive_prefix_l2_lt_last_div_nine
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:44:37.371376+00:00
-- url     : https://prove2.me/submissions/3fc6d78a-1e27-49a8-a2c9-ad81399e3e14

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
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_productFive_prefix_sq_lt_last_div_nine

section
open Matrix
open scoped NumberField

namespace D1Bound5



/-- The actual four complex entries satisfy the Euclidean norm estimate.
This uses only ordering and the proved product-four numerical growth input. -/
theorem _root_.solution
    (t : Fin 5 → ℂ)
    (hmon : Monotone (fun i => ‖t i‖))
    (hB : 3 ≤ ‖t 1‖)
    (hlarge : 2 * ‖t 1‖ * ‖t 2‖ * ‖t 3‖ < ‖t 4‖) :
    ‖(WithLp.toLp 2 (fivePrefixValues t) :
      EuclideanSpace ℂ (Fin 4))‖ < ‖t 4‖ / 9 := by
  have hab : ‖t 0‖ ≤ ‖t 1‖ := hmon (by decide)
  have hbc : ‖t 1‖ ≤ ‖t 2‖ := hmon (by decide)
  have hcs : ‖t 2‖ ≤ ‖t 3‖ := hmon (by decide)
  have hsq := productFive_prefix_sq_lt_last_div_nine
    (‖t 0‖) (‖t 1‖) (‖t 2‖) (‖t 3‖) (‖t 4‖)
    (norm_nonneg _) hab hbc hcs hB hlarge
  let w : EuclideanSpace ℂ (Fin 4) :=
    WithLp.toLp 2 (fivePrefixValues t)
  have hwsq : ‖w‖^2 =
      ‖t 0‖^2 + ‖t 1‖^2 + ‖t 2‖^2 + ‖t 3‖^2 := by
    rw [EuclideanSpace.norm_sq_eq w, Fin.sum_univ_four]
    rfl
  have hdpos : 0 < ‖t 4‖/9 := by
    have hpos : 0 ≤ 2 * ‖t 1‖ * ‖t 2‖ * ‖t 3‖ := by positivity
    linarith only [hlarge,hpos]
  have hn : 0 ≤ ‖w‖ := norm_nonneg _
  change ‖w‖ < ‖t 4‖/9
  nlinarith only [hwsq, hsq, hn, hdpos]

end D1Bound5

namespace D1Bound5



end D1Bound5
end

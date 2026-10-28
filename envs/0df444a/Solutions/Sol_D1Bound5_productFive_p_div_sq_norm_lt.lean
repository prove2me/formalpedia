-- Prove2me | solution 1 for D1Bound5.productFive_p_div_sq_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:30.183285+00:00
-- url     : https://prove2.me/submissions/e05bfc6f-cc1a-4286-8d71-8826a0fef799

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

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5



/-- If the last modulus is at least 54, the normalized p-form is smaller
than the exact rational threshold used in the determinant identity. -/
theorem _root_.solution
    (p d : ℂ) (hp : ‖p‖ < 1) (hd : 54 ≤ ‖d‖) :
    ‖p/d^2‖ < (1/2916 : ℝ) := by
  have hdpos : 0 < ‖d‖ := by linarith
  have hdsq : (2916 : ℝ) ≤ ‖d‖^2 := by
    have hn := sq_nonneg (‖d‖ - 54)
    nlinarith only [hn, hd]
  rw [norm_div, norm_pow]
  apply (div_lt_iff₀ (pow_pos hdpos 2)).mpr
  calc
    ‖p‖ < 1 := hp
    _ ≤ (1/2916 : ℝ) * ‖d‖^2 := by nlinarith only [hdsq]

end D1Bound5
end

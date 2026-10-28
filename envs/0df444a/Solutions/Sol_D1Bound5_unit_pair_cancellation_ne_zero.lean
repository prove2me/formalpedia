-- Prove2me | solution 1 for D1Bound5.unit_pair_cancellation_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:11.844332+00:00
-- url     : https://prove2.me/submissions/a676b395-a6cc-4a5c-a638-ceb1fa4ca3e2

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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The second-order unit-pair form can vanish only when the two
extensions are opposites. This calculation permits zero input roots. -/
theorem _root_.solution (u v z w : ℂ)
    (hu : u^2 = z^2+w) (hv : v^2 = z^2-w) (hw : w ≠ 0) :
    u+v-2*z ≠ 0 := by
  intro h
  have hsum : u+v = 2*z := sub_eq_zero.mp h
  have huv : u*v = z^2 := by
    linear_combination (u+v+2*z)/2 * hsum - (1/2 : ℂ)*hu - (1/2 : ℂ)*hv
  have hw2 : w^2 = 0 := by
    linear_combination (z^2-w)*hu + u^2*hv - (u*v+z^2)*huv
  exact (pow_ne_zero 2 hw) hw2











end D1Bound5
end

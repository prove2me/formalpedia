-- Prove2me | solution 1 for D1Bound5.unit_pair_cancellation_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:38.374056+00:00
-- url     : https://prove2.me/submissions/c8ef5fa6-ac2f-4f9e-9e1b-c94d38db29b1

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



/-- The first-order errors cancel exactly in the sum of the two chosen
roots; the surviving expression is quadratic in those errors. -/
theorem _root_.solution (u v z w : ℂ)
    (hu : u^2 = z^2+w) (hv : v^2 = z^2-w) :
    2*‖z‖*‖u+v-2*z‖ ≤ ‖u-z‖^2+‖v-z‖^2 := by
  have hid : 2*z*(u+v-2*z) = -((u-z)^2+(v-z)^2) := by
    linear_combination hu+hv
  have hn := congrArg norm hid
  simp only [norm_mul,norm_neg,Complex.norm_two] at hn
  rw [hn]
  calc
    _ ≤ ‖(u-z)^(2 : ℕ)‖+‖(v-z)^(2 : ℕ)‖ := norm_add_le _ _
    _ = _ := by rw [Complex.norm_pow, Complex.norm_pow]









end D1Bound5
end

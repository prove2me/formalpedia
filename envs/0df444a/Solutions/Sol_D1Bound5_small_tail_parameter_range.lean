-- Prove2me | solution 1 for D1Bound5.small_tail_parameter_range
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:40.097427+00:00
-- url     : https://prove2.me/submissions/f5e7937f-1518-4591-9158-5a0a82e784ba

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5

/-- In the normalized full integral basis, a positive discriminant at most
60 forces the remaining generator coefficient to lie between 1 and 15.
This stronger uniform rectangular reduction deliberately includes all
30 trace/parameter pairs, even models not needed for maximal orders. -/
theorem _root_.solution (tau nu : ℤ)
    (htau : tau = 0 ∨ tau = 1)
    (hpos : 0 < QuadInt.discriminant tau nu)
    (hcut : QuadInt.discriminant tau nu ≤ 60) :
    1 ≤ nu ∧ nu ≤ 15 := by
  rcases htau with rfl | rfl
  · change 0 < 4*nu-0^2 at hpos
    change 4*nu-0^2 ≤ 60 at hcut
    omega
  · change 0 < 4*nu-1^2 at hpos
    change 4*nu-1^2 ≤ 60 at hcut
    omega



end D1Bound5
end

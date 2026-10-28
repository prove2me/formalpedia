-- Prove2me | solution 1 for D1Bound5.regular_completion_cases
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:50:47.496993+00:00
-- url     : https://prove2.me/submissions/e0a2c9f0-dd28-4a7f-a0a8-e7d763bde5ac

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_Regular_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_eq_zero_iff

section
namespace D1Bound5

open QuadInt

/-- A positive-discriminant coordinate ring has no zero divisors, proved
from its positive multiplicative norm rather than assumed. -/
theorem coordinate_mul_eq_zero {tau nu : ℤ} (hd : 0 < QuadInt.discriminant tau nu)
    (a b : QuadInt tau nu) (h : a*b = 0) : a = 0 ∨ b = 0 := by
  have hn := congrArg (QuadraticAlgebra.norm : QuadInt tau nu → ℤ) h
  rw [map_mul, QuadraticAlgebra.norm_zero] at hn
  rcases mul_eq_zero.mp hn with ha | hb
  · exact Or.inl ((QuadInt.norm_eq_zero_iff hd a).mp ha)
  · exact Or.inr ((QuadInt.norm_eq_zero_iff hd b).mp hb)

/-- Every regular completion is one of the two completions formed from
any chosen root of bc+1. Zero roots cause no exception. -/
theorem _root_.solution {tau nu : ℤ} (hd : 0 < QuadInt.discriminant tau nu)
    (b c d r : QuadInt tau nu) (hr : r*r = b*c+1) (hreg : regularDefect b c d = 0) :
    d = b+c+2*r ∨ d = b+c-2*r := by
  have hp : (d-b-c-2*r)*(d-b-c+2*r) = 0 := by
    unfold regularDefect at hreg
    linear_combination hreg-4*hr
  rcases coordinate_mul_eq_zero hd _ _ hp with h | h
  · left
    linear_combination h
  · right
    linear_combination h










end D1Bound5
end

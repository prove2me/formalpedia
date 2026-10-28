-- Prove2me | solution 1 for D1Bound5.pairNegativeIntegerObstructionBool_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:15.144392+00:00
-- url     : https://prove2.me/submissions/df678c7c-9056-456a-8fc8-e4caad290a9b

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairNegativeIntegerObstruction_Definitions
import Theorems.Thm_D1Bound5_negative_integer_square_dvd_trace_one
import Theorems.Thm_D1Bound5_negative_integer_square_dvd_trace_zero

section
namespace D1Bound5









/-- A successful negative-integer obstruction excludes every square root.
In particular, rejection cannot discard a genuine zero root. -/
theorem _root_.solution {tau nu : ℤ}
    (z : QuadInt tau nu) (h : pairNegativeIntegerObstructionBool z = true) :
    ¬ ∃ r : QuadInt tau nu, r * r = z := by
  unfold pairNegativeIntegerObstructionBool at h
  have hparts := Bool.and_eq_true_iff.mp h
  have hsign : z.im = 0 ∧ z.re < 0 := of_decide_eq_true hparts.1
  intro hsquare
  by_cases ht : tau = 0
  · have hfail : ¬ nu ∣ z.re :=
      of_decide_eq_true (by simpa only [if_pos ht] using hparts.2)
    subst tau
    exact hfail (negative_integer_square_dvd_trace_zero z hsign.1 hsign.2 hsquare)
  · by_cases ht1 : tau = 1
    · have hfail : ¬ (4 * nu - 1) ∣ z.re :=
        of_decide_eq_true (by simpa only [if_neg ht, if_pos ht1] using hparts.2)
      subst tau
      exact hfail (negative_integer_square_dvd_trace_one z hsign.1 hsign.2 hsquare)
    · simpa only [if_neg ht, if_neg ht1, Bool.false_eq_true] using hparts.2

end D1Bound5
end

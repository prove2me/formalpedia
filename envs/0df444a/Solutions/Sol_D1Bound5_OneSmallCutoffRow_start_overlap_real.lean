-- Prove2me | solution 1 for D1Bound5.OneSmallCutoffRow.start_overlap_real
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:34.597124+00:00
-- url     : https://prove2.me/submissions/9a7f02a4-dbf9-475f-b5fe-08e6daac25ac

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_OneSmallCutoffRow_overlaps_at_real

section
namespace D1Bound5



/-- The first table inequality is exactly the strict overlap of the
retained direct-four start with the finite Q interval. -/
theorem _root_.solution (r : OneSmallCutoffRow)
    (hv : r.Valid) (S T : ℝ) (hS : 0 < S)
    (hSsq : S^2 = (r.s0 : ℝ))
    (hlarge : (r.triple.cutoff : ℝ) ≤ T^2) :
    1 < (1-1/4000 : ℝ)*(r.retainedCoefficient : ℝ)^4*T^10/(12100*S^10) := by
  have h := r.overlaps_at_real hv (T^2) hlarge
    (((1-1/4000)*r.retainedCoefficient^4/(12100*r.s0^5)),5)
    (by simp [OneSmallCutoffRow.overlaps])
  change 1 < (((1-1/4000)*r.retainedCoefficient^4/(12100*r.s0^5) : ℚ) : ℝ)*
    (T^2)^5 at h
  push_cast at h
  rw [←hSsq] at h
  convert h using 1 <;> ring



end D1Bound5
end

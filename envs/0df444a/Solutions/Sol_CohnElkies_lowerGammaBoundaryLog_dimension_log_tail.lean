-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_dimension_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/c4ead827-c71c-4a4b-8f73-6990552324e8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer_log_tail
import Theorems.Thm_CohnElkies_lowerCoth_log_nonneg
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger_log_tail

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (_hd : 0 < d) {R y : ℝ}
    (hR : 0 < R) (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R y ≤
      ((d : ℝ) / 2) * Real.log
        (2 * Real.pi * R ^ 2 / |y|) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |y| / 2)) := by
  have hcoth : 0 ≤ Real.log
      (lowerCoth (Real.pi * |y| / 2)) := by
    apply lowerCoth_log_nonneg
    positivity
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hq : ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    rw [hq]
    have htail := lowerGammaBoundaryLog_integer_log_tail k hR hy
    linarith
  · have hq : ((↑(2 * k + 1) : ℝ) / 2) =
        (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_halfInteger_log_tail k hR hy
end CohnElkies

-- Prove2me | solution 1 for CohnElkies.upper_min_frequency_inverse_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/173b4153-242b-4d7e-a890-9748951f613c

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {a : ℝ} (ha : 0 < a) (T : ℝ) :
    min (T ^ 2) ((a ^ 2)⁻¹) ≤
      min (T ^ 2) 1 * (1 + (a ^ 2)⁻¹) := by
  have hinv : 0 ≤ (a ^ 2)⁻¹ := by positivity
  by_cases hsmall : T ^ 2 ≤ 1
  · rw [min_eq_left hsmall]
    have hmin := min_le_left (T ^ 2) ((a ^ 2)⁻¹)
    nlinarith [mul_nonneg (sq_nonneg T) hinv]
  · rw [min_eq_right (le_of_not_ge hsmall)]
    have hmin := min_le_right (T ^ 2) ((a ^ 2)⁻¹)
    nlinarith
end CohnElkies

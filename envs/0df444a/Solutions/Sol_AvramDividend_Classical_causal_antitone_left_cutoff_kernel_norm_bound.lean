-- Prove2me | solution 1 for AvramDividend.Classical.causal_antitone_left_cutoff_kernel_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:50:49.312934+00:00
-- url     : https://prove2.me/submissions/825856c6-7c82-4d7b-bb25-3239b925bf29

import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A nonnegative antitone kernel is uniformly bounded away from its singular origin. -/
theorem solution
    (κ : ℝ → ℝ) (x u s : ℝ)
    (hu : 0 < u) (hux : u < x)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hKnonneg : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hs : s ∈ Ioc (0 : ℝ) u) :
    ‖κ (x - s)‖ ≤ κ (x - u) := by
  have hxumin : 0 < x - u := sub_pos.mpr hux
  have hxs : 0 < x - s := by
    have hsu : s ≤ u := hs.2
    linarith
  have hle : x - u ≤ x - s := by linarith [hs.2]
  have hbound : κ (x - s) ≤ κ (x - u) :=
    hanti hxumin hxs hle
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hKnonneg (x - s) hxs)] using hbound

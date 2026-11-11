-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin26_original_reward_nonnegative_below_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:01:23.836881+00:00
-- url     : https://prove2.me/submissions/003a87d4-15dd-4dd8-82e2-13ab840e1791

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_positive_initial_from_closed_cap_gradient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (v : ℝ) (hv : 0 < v) (hvC : ENNReal.ofReal v < C) :
    ∀ t : ℝ, t ≤ v → 0 ≤ w t := by
  intro t ht
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · rw [hw_neg t hneg]
  · subst t
    exact hw0
  · have htc : ENNReal.ofReal t ≤ C :=
      (ENNReal.ofReal_le_ofReal ht).trans (le_of_lt hvC)
    exact avram_mix_fin22_positive_initial_from_closed_cap_gradient
      C hC w hw0 hw_cont hw_smooth hw_grad t hpos htc

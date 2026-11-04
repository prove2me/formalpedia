-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_test_vanishes_on_nonnegative_image
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:01:19.78154+00:00
-- url     : https://prove2.me/submissions/20060355-96cc-435d-811c-496e549441b7

import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε)
    (f : ℝ → ℝ) (hf : ∀ y : ℝ, -ε < y → f y = 0)
    (z : ℝ) (hz : 1 ≤ z) :
    f (Real.log z / θ) / (z - 1) ^ 4 = 0 := by
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz
  have hquot : 0 ≤ Real.log z / θ :=
    div_nonneg hlog (le_of_lt hθ)
  have hband : -ε < Real.log z / θ := by linarith
  rw [hf _ hband]
  simp

-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_weighted_log_positive_band_test
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:36:04.013618+00:00
-- url     : https://prove2.me/submissions/560df18d-5c85-42c9-af64-a68d90cf6fa4

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_continuous_all_real
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_zero_outside_positive_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set

/-- A negative-mark logarithmic test vanishes on a positive neighbourhood of zero and above one. -/
theorem solution
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    Continuous (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) ∧
    ∃ δ : ℝ, 0 < δ ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ δ →
        f (Real.log z) / (z - 1) ^ 4 = 0) ∧
      (∀ z : ℝ, 1 ≤ z →
        f (Real.log z) / (z - 1) ^ 4 = 0) := by
  refine ⟨AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_continuous_all_real
    f hf a ε hε hflower hfupper, ⟨Real.exp a / 2, by positivity, ?_, ?_⟩⟩
  · intro z hz hzδ
    have hexp : 0 < Real.exp a := Real.exp_pos a
    have hbelow : z < Real.exp a := by linarith
    exact AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_zero_outside_positive_band
      f a ε hε hflower hfupper z hz (Or.inl hbelow)
  · intro z hz
    have hneg : -ε < 0 := by linarith
    have hupper : Real.exp (-ε) < (1 : ℝ) :=
      Real.exp_lt_one_iff.mpr hneg
    exact AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_zero_outside_positive_band
      f a ε hε hflower hfupper z (by linarith)
      (Or.inr (lt_of_lt_of_le hupper hz))

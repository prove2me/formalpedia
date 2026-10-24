-- Prove2me | solution 1 for AvramDividend.Classical.integrable_ramp_mul_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:36:11.508994+00:00
-- url     : https://prove2.me/submissions/1a4ac500-4e8d-477c-b589-be66ceafc39d

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A clipped ramp acts as an L1-bounded multiplication operator. -/
theorem solution
    (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : Integrable f volume) :
    Integrable (fun x : ℝ => max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x) volume := by
  obtain ⟨hχ, _, _⟩ := positive_ramp_cutoff_continuous_and_support ε hε
  apply hf.bdd_mul hχ.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    have hχ0 : 0 ≤ max (0 : ℝ) (min 1 ((x - ε) / ε)) := le_max_left _ _
    have hχ1 : max (0 : ℝ) (min 1 ((x - ε) / ε)) ≤ 1 :=
      max_le (by norm_num) (min_le_left _ _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hχ0] using hχ1

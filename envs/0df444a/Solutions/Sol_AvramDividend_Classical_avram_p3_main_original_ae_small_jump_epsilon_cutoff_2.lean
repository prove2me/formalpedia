-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_main_original_ae_small_jump_epsilon_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:07:11.953392+00:00
-- url     : https://prove2.me/submissions/b331080f-0d57-4628-bd3e-308d3e2863d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_small_jump_epsilon_cutoff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal BigOperators

/-- Transfer the original almost-sure BV jump summability to the
    source-time-indexed epsilon-small jump cutoff on one common full event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let j : ℝ≥0 → ℝ := fun u =>
        if 0 < u ∧ u ≤ T then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          (∑' u : ℝ≥0, if |j u| < δ then |j u| else 0) < ε := by
  classical
  filter_upwards
    [avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable
      X hBV] with ω hω
  exact avram_p3_main_original_small_jump_epsilon_cutoff
    (fun u : ℝ≥0 =>
      if (0 : ℝ≥0) < u ∧ u ≤ T then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
      else 0)
    (hω 0 T (show (0 : ℝ≥0) ≤ T from zero_le))

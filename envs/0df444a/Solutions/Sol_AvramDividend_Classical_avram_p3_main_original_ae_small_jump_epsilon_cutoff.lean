-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_ae_small_jump_epsilon_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:06:23.862481+00:00
-- url     : https://prove2.me/submissions/9be5ffb0-42d6-4a2b-a479-a4ce85d0539d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_small_jump_epsilon_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal BigOperators

/-- One probability-one original BV event has arbitrarily small absolute
negative source-left-jump mass below a positive mark cutoff on every
chosen strict finite observation interval. -/
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
  filter_upwards
    [avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable X hBV]
      with ω hω
  let j : ℝ≥0 → ℝ := fun u =>
    if 0 < u ∧ u ≤ T then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
    else 0
  have h0 : (0 : ℝ≥0) ≤ T := bot_le
  have hj : Summable (fun u : ℝ≥0 => |j u|) := by
    simpa only [j] using (hω 0 T h0)
  change ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      (∑' u : ℝ≥0, if |j u| < δ then |j u| else 0) < ε
  intro ε hε
  exact avram_p3_main_original_small_jump_epsilon_cutoff j hj ε hε

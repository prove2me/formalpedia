-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:40:13.293214+00:00
-- url     : https://prove2.me/submissions/cdae12ef-635f-42e1-b68d-532a2044dca5

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_real_jump_total_monotone_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV real cumulative negative jump sum is monotone without casts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 =>
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_real_jump_total_monotone_time X hBV,
      avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
    with ω hmono hreal
  intro s t hst
  have h0s : (0 : ℝ≥0) ≤ s := zero_le
  have h0t : (0 : ℝ≥0) ≤ t := zero_le
  have hs := (hreal 0 s h0s).2
  have ht := (hreal 0 t h0t).2
  have hle := hmono hst
  change
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
      ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
      else 0).toReal ≤
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
      ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
      else 0).toReal at hle
  rw [hs, ht] at hle
  exact hle

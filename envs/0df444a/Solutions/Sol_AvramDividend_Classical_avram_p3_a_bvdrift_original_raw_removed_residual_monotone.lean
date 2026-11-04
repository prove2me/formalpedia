-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:16:37.232351+00:00
-- url     : https://prove2.me/submissions/686cbe8e-c178-41ec-acf4-d73c2048892a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine source BV residual is monotone when its actual negative
jumps are expressed directly as a signed real tsum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 =>
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0))) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_canonical_remainder_monotone X hBV,
     avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
    with ω hmono hraw
  intro s t hst
  have h := hmono hst
  dsimp only at h
  rw [(hraw 0 s (show (0 : ℝ≥0) ≤ s from zero_le)).2,
      (hraw 0 t (show (0 : ℝ≥0) ≤ t from zero_le)).2] at h
  exact h

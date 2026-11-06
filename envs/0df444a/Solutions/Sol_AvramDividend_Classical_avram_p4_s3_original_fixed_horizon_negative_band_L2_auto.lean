-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_fixed_horizon_negative_band_L2_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:18:35.851518+00:00
-- url     : https://prove2.me/submissions/edcbb7d7-cfd0-4520-a459-e90aa0d3078c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_square_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_ncard_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original negative-band jump count on every deterministic horizon is in L². -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    MemLp (fun ω : Ω => ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard : ℝ)) 2 P := by
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  change MemLp (fun ω => (K ω : ℝ)) 2 P
  have hKm : Measurable K :=
    avram_p4_f2_original_negative_band_ncard_measurable X T n
  have hK2 : Integrable (fun ω => (K ω : ℝ) ^ 2) P :=
    (avram_p4_s3_original_bounded_stop_negative_band_square_budget
      X T n (fun _ => T) (fun _ => le_rfl) hKm).1
  have hKr : Measurable (fun ω => (K ω : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hKm
  exact (memLp_two_iff_integrable_sq hKr.aestronglyMeasurable).2 hK2

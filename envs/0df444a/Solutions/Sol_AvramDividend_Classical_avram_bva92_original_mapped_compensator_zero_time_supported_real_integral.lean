-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:54:54.61781+00:00
-- url     : https://prove2.me/submissions/45bc0079-171c-4764-a1ff-9a13fd8fc2f4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva91_original_mapped_levy_compensator_time_zero_atom_null_any_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (S : ℝ≥0) (f : ℝ≥0 → ℝ)
    (hSupport : ∀ t : ℝ≥0, t ≠ 0 → f t = 0) :
    (∫ t, f t
      ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal)) = 0 := by
  let μ : Measure ℝ≥0 :=
    (((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal)
  have hNull : μ ({0} : Set ℝ≥0) = 0 :=
    avram_bva91_original_mapped_levy_compensator_time_zero_atom_null_any_horizon S
  have hBad : {t : ℝ≥0 | ¬ t ≠ 0} = ({0} : Set ℝ≥0) := by
    ext t
    simp
  have hAE : ∀ᵐ t ∂μ, t ≠ 0 := by
    apply (ae_iff).2
    simpa only [hBad] using hNull
  change (∫ t, f t ∂μ) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [hAE] with t ht
  exact hSupport t ht

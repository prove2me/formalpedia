-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_cutoff_residual_integrable_centered_finite_measure_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:27:33.693137+00:00
-- url     : https://prove2.me/submissions/e085e647-24cc-4eb2-91d2-7553e4e69681

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- All physical cutoffs are integrable and centred on finite probability measures. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P ∧
      (∫ ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω ∂P) = 0 := by
  intro n t
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
  have hNegMeas : Measurable (fun ω => -J ω) :=
    (avram_ja21_original_gaussian_core_and_jump_cutoff_measurable X n t).2.mono
      (𝓕.le t) le_rfl
  have hJmeas : AEStronglyMeasurable J P := by
    have h := hNegMeas.neg.aestronglyMeasurable (μ := P)
    change AEStronglyMeasurable (fun ω => -(-(J ω))) P at h
    simpa only [neg_neg] using h
  have hJ2 : Integrable (fun ω => (J ω)^2) P :=
    avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
      X hFinite n t
  have hJmem : MemLp J 2 P :=
    (memLp_two_iff_integrable_sq hJmeas).2 hJ2
  have hJ : Integrable J P :=
    hJmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
    X hX hFinite n t hJ

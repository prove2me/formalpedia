-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:25:09.522386+00:00
-- url     : https://prove2.me/submissions/d4fd0799-6471-47cb-9b64-f019faf9681f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_uniform_quadratic_envelope
import Theorems.Thm_AvramDividend_Classical_avram_anoise33_original_smallband_compensator_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- An original-space square-integrable count envelope dominates each fixed band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (t : ℝ≥0) :
    Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2) P := by
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
  have hJ : Measurable J :=
    (avram_anoise33_original_smallband_compensator_adapted
      X n t).mono (𝓕.le t) le_rfl
  obtain ⟨B, hBint, hbound⟩ :=
    avram_ja19_original_smallband_uniform_quadratic_envelope X hFinite t
  apply hBint.mono' (hJ.pow_const 2).aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  have hle : ‖J ω‖ ≤ B ω := hω n t le_rfl
  have hBnonneg : 0 ≤ B ω := le_trans (norm_nonneg _) hle
  have hsq : ‖J ω‖ ^ 2 ≤ (B ω) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hle)
      (add_nonneg hBnonneg (norm_nonneg (J ω)))]
  simpa only [norm_pow, Real.norm_eq_abs, abs_of_nonneg hBnonneg] using hsq

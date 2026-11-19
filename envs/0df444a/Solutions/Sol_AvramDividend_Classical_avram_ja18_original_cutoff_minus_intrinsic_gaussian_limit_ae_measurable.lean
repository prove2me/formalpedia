-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_cutoff_minus_intrinsic_gaussian_limit_ae_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:16:37.380148+00:00
-- url     : https://prove2.me/submissions/5be3a2e0-b1b4-4740-92be-07da2540afa5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original cutoff residual minus the true Gaussian limit is measurable at each fixed time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hRmeas : ∀ t : ℝ≥0, AEStronglyMeasurable (R t) P) :
    ∀ (n : ℕ) (t : ℝ≥0),
      AEStronglyMeasurable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) P := by
  intro n t
  have hCore := avram_ja21_original_gaussian_core_and_jump_cutoff_measurable X n t
  have hCut : Measurable[𝓕 t]
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) := by
    have heq : (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) =
        (fun ω =>
          (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
           avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) +
          -avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) := by
      funext ω
      simpa only [sub_eq_add_neg] using
        (avram_ja21_original_cutoff_residual_gaussian_core_split X n t ω)
    rw [heq]
    exact hCore.1.add hCore.2
  have hm : Measurable (fun ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) :=
    hCut.mono (𝓕.le t) le_rfl
  exact hm.aestronglyMeasurable.sub (hRmeas t)

-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:06:25.344975+00:00
-- url     : https://prove2.me/submissions/2ede1a2c-c5f9-4a11-b497-255854e7b42b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_intrinsic_limit_ae_rightCont_measurable_of_cutoffs
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Intrinsic same-space Gaussian residual has a compact-uniform, original-filtration AE-adapted limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P,
        (∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
            atTop (nhds (R T ω))) ∧
        (∀ K : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
              |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
                R T ω| ≤ η)) ∧
      (∀ T : ℝ≥0,
        AEStronglyMeasurable[𝓕.rightCont T] (R T) P) := by
  apply avram_mix_gauss14_intrinsic_limit_ae_rightCont_measurable_of_cutoffs X hFinite
  intro n T
  exact (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted X n T).mono
    (𝓕.le_rightCont T) le_rfl

-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_every_cutoff_residual_integrable_centered_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:27:03.115207+00:00
-- url     : https://prove2.me/submissions/cfbf3323-07f9-4ef6-a330-9696e4715d95

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_retained_compensated_negative_band_L1_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every physical Gaussian residual cutoff is integrable and centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P ∧
      (∫ ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω ∂P) = 0 := by
  intro n t
  exact avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
    X hX hFinite n t
    (avram_a21_original_retained_compensated_negative_band_L1_20261113
      X hFinite n t)

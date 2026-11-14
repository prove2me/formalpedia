-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_uniform_every_gaussian_cutoff_future_borel_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:36:52.910249+00:00
-- url     : https://prove2.me/submissions/39d5b0a0-89bd-422f-ae40-018604dab0ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_zero_cutoff_future_borel_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_compensated_band_future_borel_20261113
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every original Gaussian residual cutoff has the same Borel future-path increment functional at all starts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ (s : ℝ≥0) (ω : Ω),
        avram_p4_h_gaussian_intrinsic_truncated_residual X n (s + T) ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω =
        W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
  obtain ⟨W0, hW0, hBase⟩ :=
    avram_a24_uniform_zero_cutoff_future_borel_20261113 X hX hFinite T
  obtain ⟨WB, hWB, hBand⟩ :=
    avram_a24_uniform_compensated_band_future_borel_20261113 X n T
  let W : (ℝ≥0 → ℝ) → ℝ := fun Y => W0 Y - WB Y
  refine ⟨W, hW0.sub hWB, ?_⟩
  intro s ω
  have hCutT := avram_ja21_original_cutoff_residual_gaussian_core_split
    X n (s + T) ω
  have hCutS := avram_ja21_original_cutoff_residual_gaussian_core_split
    X n s ω
  have hZeroT :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
      X (s + T) ω
  have hZeroS :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
      X s ω
  change _ = W0 (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) -
    WB (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω)
  calc
    avram_p4_h_gaussian_intrinsic_truncated_residual X n (s + T) ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω =
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 (s + T) ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω) -
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s + T) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) := by
      rw [hCutT, hCutS, hZeroT, hZeroS]
      ring
    _ = W0 (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) -
      WB (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
      rw [hBase s ω, hBand s ω]

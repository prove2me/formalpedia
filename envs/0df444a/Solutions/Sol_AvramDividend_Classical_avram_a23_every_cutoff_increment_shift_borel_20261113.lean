-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_every_cutoff_increment_shift_borel_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:12:49.259807+00:00
-- url     : https://prove2.me/submissions/356507f1-4947-448d-84cf-ae3840505f8f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_intrinsic_residual_increment_shift_borel
import Theorems.Thm_AvramDividend_Classical_avram_a23_original_smallband_increment_shift_borel_20261113
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original Gaussian cutoff increments depend measurably on the original shifted future path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ ω : Ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω =
        W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
  obtain ⟨W0, hW0, hBase⟩ :=
    avram_ja18h_original_intrinsic_residual_increment_shift_borel
      X hX hFinite s t hst
  obtain ⟨WB, hWB, hBand⟩ :=
    avram_a23_original_smallband_increment_shift_borel_20261113
      X n s t hst
  let W : (ℝ≥0 → ℝ) → ℝ := fun Y => W0 Y - WB Y
  refine ⟨W, hW0.sub hWB, ?_⟩
  intro ω
  have hCutT := avram_ja21_original_cutoff_residual_gaussian_core_split
    X n t ω
  have hCutS := avram_ja21_original_cutoff_residual_gaussian_core_split
    X n s ω
  have hZeroT :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
      X t ω
  have hZeroS :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
      X s ω
  change _ = W0 (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) -
    WB (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω)
  calc
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω =
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω) -
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) := by
      rw [hCutT, hCutS, hZeroT, hZeroS]
      ring
    _ = W0 (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) -
      WB (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
      rw [hBase ω, hBand ω]

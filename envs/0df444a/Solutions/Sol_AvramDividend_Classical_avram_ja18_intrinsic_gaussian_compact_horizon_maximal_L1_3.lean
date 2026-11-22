-- Prove2me | solution 3 for AvramDividend.Classical.avram_ja18_intrinsic_gaussian_compact_horizon_maximal_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:23:45.18344+00:00
-- url     : https://prove2.me/submissions/4350398d-2ee1-4ec0-a9c3-c96c38f4829e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finiteactivity_zero_cutoff_physical_square_L1
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_anoise23_original_residual_square_integrable_of_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (nhds (R t ω)))
    (n : ℕ) (hn : 0 < n) :
    ∃ B : Ω → ℝ,
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        ‖R t ω‖ ≤ B ω)  := by
  have hSource : ∀ᵐ ω ∂P,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j (n : ℝ≥0) ω)
        atTop (nhds (R (n : ℝ≥0) ω)) := by
    filter_upwards [hR] with ω hω
    exact hω n
  have hCutMeas (j : ℕ) :
      AEStronglyMeasurable
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X j (n : ℝ≥0) ω)
        P := by
    exact ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X j (n : ℝ≥0)).mono (𝓕.le _) le_rfl).aestronglyMeasurable
  have hRmeas : AEStronglyMeasurable (R (n : ℝ≥0)) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hCutMeas hSource
  have hCutSquare : Integrable
      (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual
        X 0 (n : ℝ≥0) ω) ^ 2) P :=
    avram_jump6_A_original_finiteactivity_zero_cutoff_physical_square_L1
      X hX hFinite (n : ℝ≥0)
  have hSquare : Integrable (fun ω => (R (n : ℝ≥0) ω) ^ 2) P :=
    avram_anoise23_original_residual_square_integrable_of_cutoff
      X hFinite R (n : ℝ≥0) hSource hRmeas hCutMeas hCutSquare
  exact avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
    X hX hFinite R hR n hn hSquare

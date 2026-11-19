-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja18_intrinsic_gaussian_compact_horizon_maximal_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:55:33.685944+00:00
-- url     : https://prove2.me/submissions/693e1430-420f-49cc-ae3b-497b51a455ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
import Theorems.Thm_AvramDividend_Classical_avram_anoise23_original_residual_square_integrable_of_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finiteactivity_zero_cutoff_physical_square_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
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
        ‖R t ω‖ ≤ B ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨G, hGmeas, hG0, hGEq, hGcont, hGind, hGstation, hGint, hGcond⟩ :=
    avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
      X hX hFinite R hR
  have hRmeas : AEStronglyMeasurable (R (n : ℝ≥0)) P := by
    have hGm : AEStronglyMeasurable (G (n : ℝ≥0)) P :=
      (((hGmeas (n : ℝ≥0)).mono
        (𝓕.le (n : ℝ≥0)) le_rfl).aestronglyMeasurable)
    apply hGm.congr
    filter_upwards [hGEq] with ω hω
    exact hω (n : ℝ≥0)
  have hCutMeas : ∀ j : ℕ, AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X j (n : ℝ≥0) ω) P := by
    intro j
    exact (((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X j (n : ℝ≥0)).mono (𝓕.le (n : ℝ≥0)) le_rfl)).aestronglyMeasurable
  have hCutSquare :=
    avram_jump6_A_original_finiteactivity_zero_cutoff_physical_square_L1
      X hX hFinite (n : ℝ≥0)
  have hRsourceT : ∀ᵐ ω ∂P,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j (n : ℝ≥0) ω)
        atTop (nhds (R (n : ℝ≥0) ω)) := by
    filter_upwards [hR] with ω hω
    exact hω (n : ℝ≥0)
  have hSquare : Integrable (fun ω => (R (n : ℝ≥0) ω) ^ 2) P :=
    avram_anoise23_original_residual_square_integrable_of_cutoff
      X hFinite R (n : ℝ≥0) hRsourceT hRmeas hCutMeas hCutSquare
  exact avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
    X hX hFinite R hR n hn hSquare

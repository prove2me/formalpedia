-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_positive_time_positive_cutoff_residual_retained_cross_zero_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:20:50.856454+00:00
-- url     : https://prove2.me/submissions/0ea2787d-4a27-4ad2-b3ac-eb080dcdcfea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_positive_time_disjoint_cutoff_residual_retained_independence_L1_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_smallband_cutoff_centered
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The true disjoint-noise independence gives original-space source covariance zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      let R : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω
      Integrable (fun ω => R ω * J ω) P ∧
        (∫ ω, R ω * J ω ∂P) = 0 := by
  intro n t ht
  let R : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω
  have hInd :=
    avram_a21_positive_time_disjoint_cutoff_residual_retained_independence_L1_20261113
      X hX hFinite n t ht
  change ProbabilityTheory.IndepFun R J P ∧ Integrable J P at hInd
  have hRCent :=
    avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
      X hX hFinite (n + 1) t hInd.2
  change Integrable R P ∧ _ at hRCent
  have hJCent : (∫ ω, J ω ∂P) = 0 := by
    have h := avram_ja21_original_smallband_cutoff_centered
      X hX hFinite (n + 1) t
    change (∫ ω, -J ω ∂P) = 0 at h
    rw [integral_neg] at h
    exact neg_eq_zero.mp h
  have hMul : Integrable (fun ω => R ω * J ω) P := by
    exact hInd.1.integrable_mul hRCent.1 hInd.2
  have hEq := hInd.1.integral_fun_mul_eq_mul_integral
    hRCent.1.1 hInd.2.1
  change (∫ ω, R ω * J ω ∂P) =
    (∫ ω, R ω ∂P) * (∫ ω, J ω ∂P) at hEq
  rw [hJCent, mul_zero] at hEq
  exact ⟨hMul, hEq⟩

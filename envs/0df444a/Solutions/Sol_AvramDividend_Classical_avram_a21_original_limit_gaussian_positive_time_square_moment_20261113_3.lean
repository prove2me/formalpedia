-- Prove2me | solution 3 for AvramDividend.Classical.avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:47:02.152205+00:00
-- url     : https://prove2.me/submissions/c3631473-c22b-4788-b9ab-4c8cc7e40836
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ t : ℝ≥0, 0 < t →
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by
  intro t ht
  by_cases hZero : X.σ = 0
  · have hZeroAll :=
      avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
        X hX hFinite R hR hZero
    have hAE : ∀ᵐ ω ∂P, R t ω = 0 := by
      filter_upwards [hZeroAll] with ω hω
      exact hω t
    have hInt : Integrable (fun ω => (R t ω) ^ 2) P := by
      have hIntZero : Integrable (fun _ : Ω => (0 : ℝ)) P := by simp
      apply hIntZero.congr
      filter_upwards [hAE] with ω hω
      simp [hω]
    refine ⟨hInt, ?_⟩
    calc
      (∫ ω, (R t ω) ^ 2 ∂P) =
          (∫ _ : Ω, (0 : ℝ) ∂P) := by
            apply integral_congr_ae
            filter_upwards [hAE] with ω hω
            simp [hω]
      _ = (t : ℝ) * X.σ ^ 2 := by simp [hZero]
  · have hPositive : 0 < X.σ :=
      lt_of_le_of_ne X.σ_nonneg (Ne.symm hZero)
    have hEq : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, R u ω = R u ω :=
      Filter.Eventually.of_forall (fun _ _ => rfl)
    have hLaw :=
      avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
        X hX hFinite hPositive R hR R hEq t
    let v : NNReal :=
      NNReal.mk ((t : ℝ) * X.σ ^ 2)
        (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ))
    have hGaussianSq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
      simpa only [id_eq] using
        (memLp_id_gaussianReal (μ := 0) (v := v) (2 : NNReal)).integrable_sq
    have hIntMap : Integrable (fun x : ℝ => x ^ 2) (P.map (R t)) := by
      rw [hLaw.map_eq]
      exact hGaussianSq
    have hInt : Integrable (fun ω => (R t ω) ^ 2) P :=
      hIntMap.comp_aemeasurable hLaw.aemeasurable
    have hMean : (∫ ω, R t ω ∂P) = 0 := by
      simpa using hLaw.integral_eq.trans integral_id_gaussianReal
    have hVariance : variance (R t) P = (t : ℝ) * X.σ ^ 2 := by
      rw [hLaw.variance_eq, variance_id_gaussianReal]
      change (v : ℝ) = (t : ℝ) * X.σ ^ 2
      simpa only [v, NNReal.coe_mk]
    refine ⟨hInt, ?_⟩
    rw [← variance_of_integral_eq_zero hLaw.aemeasurable hMean, hVariance]

-- Prove2me | solution 4 for AvramDividend.Classical.avram_anoise22_original_gaussian_cutoff_exact_second_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:58:37.457569+00:00
-- url     : https://prove2.me/submissions/32f08ad8-b372-426e-8b7f-d95fc573fedb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_intrinsic_limit_ae_adapted_of_cutoff_convergence
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_omitted_nearzero_tail_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_omitted_tail_zero_cross
import Theorems.Thm_AvramDividend_Classical_avram_ja19_square_integrable_of_ae_sum_components
import Theorems.Thm_AvramDividend_Classical_avram_ja20_integrable_product_of_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja20_integral_square_sum_uncorrelated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every original cutoff second moment from Gaussian limit and omitted-tail orthogonality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      let R0 : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω
      Integrable (fun ω => (R0 ω)^2) P ∧
        (∫ ω, (R0 ω)^2 ∂P) =
          (t : ℝ) * X.σ ^ 2 +
            (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  intro n t
  let R0 : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω
  obtain ⟨R, hR⟩ :=
    avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
      X hFinite
  have hRsource : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
        atTop (nhds (R T ω)) := by
    filter_upwards [hR] with ω hω
    exact hω.1
  have hCut (n : ℕ) (T : ℝ≥0) :
      Measurable[𝓕.rightCont T]
        (fun ω : Ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) :=
    (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n T).mono (𝓕.le_rightCont T) le_rfl
  have hRmeas : AEStronglyMeasurable (R t) P :=
    (avram_mix_inf15_original_intrinsic_limit_ae_adapted_of_cutoff_convergence
      X hCut R hRsource t).mono ((𝓕.rightCont).le t)
  have hCutmeas : AEStronglyMeasurable R0 P :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  let J : Ω → ℝ := fun ω => R0 ω - R t ω
  have hJmeas : AEStronglyMeasurable J P := hCutmeas.sub hRmeas
  have hGsq :=
    avram_ja22_original_limit_gaussian_exact_square_moment
      X hX hFinite R hRsource t
  have hJsq :=
    avram_ja22_original_omitted_nearzero_tail_exact_square_moment
      X hX hFinite R hRsource n t
  change Integrable (fun ω => (J ω)^2) P ∧ _ at hJsq
  have hCross :=
    avram_ja22_original_limit_gaussian_omitted_tail_zero_cross
      X hX hFinite R hRsource n t
  change (∫ ω, R t ω * J ω ∂P) = 0 at hCross
  have hProd : Integrable (fun ω => R t ω * J ω) P :=
    avram_ja20_integrable_product_of_square_integrable
      P (R t) J hRmeas hJmeas hGsq.1 hJsq.1
  have hASq : Integrable (fun ω => (R0 ω)^2) P := by
    apply avram_ja19_square_integrable_of_ae_sum_components
      R0 (R t) J hCutmeas hGsq.1 hJsq.1
    filter_upwards [] with ω
    dsimp [J]
    ring
  have hEnergy :=
    avram_ja20_integral_square_sum_uncorrelated
      P (R t) J ((t : ℝ) * X.σ ^ 2)
        ((t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν))
      hGsq.1 hJsq.1 hProd hCross hGsq.2 (by simpa using hJsq.2)
  change (∫ ω, (R t ω + J ω) ^ 2 ∂P) = _ at hEnergy
  have hEq : (fun ω => R t ω + J ω) = R0 := by
    funext ω
    dsimp [J]
    ring
  have hEqSquare : (fun ω => (R t ω + J ω) ^ 2) =
      (fun ω => (R0 ω) ^ 2) := by
    funext ω
    rw [congrFun hEq ω]
  rw [hEqSquare] at hEnergy
  exact ⟨hASq, hEnergy⟩

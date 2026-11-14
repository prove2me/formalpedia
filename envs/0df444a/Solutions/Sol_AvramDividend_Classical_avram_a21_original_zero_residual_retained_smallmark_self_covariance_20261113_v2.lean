-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_zero_residual_retained_smallmark_self_covariance_20261113_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:23.601513+00:00
-- url     : https://prove2.me/submissions/18d0b8f6-1965-45b5-9431-71553e32160f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_cutoff_residual_retained_band_cross_zero_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Cross covariance follows by expanding the genuine retained-strip subtraction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      let R0 : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
      Integrable (fun ω => (J ω)^2) P ∧
      Integrable (fun ω => R0 ω * J ω) P ∧
        (∫ ω, R0 ω * J ω ∂P) =
          (∫ ω, (J ω)^2 ∂P) := by
  intro n t
  let R0 : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω
  let Rn : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
  have hOrth :=
    avram_a21_original_cutoff_residual_retained_band_cross_zero_20261113
      X hX hFinite n t
  change Integrable (fun ω => Rn ω * J ω) P ∧
      (∫ ω, Rn ω * J ω ∂P) = 0 at hOrth
  have hJ2 :=
    avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
      X hFinite n t
  change Integrable (fun ω => (J ω)^2) P at hJ2
  have hPath (ω : Ω) : R0 ω = Rn ω + J ω := by
    have h := avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
      X n t ω
    change Rn ω = R0 ω - J ω at h
    linarith
  have hFun : (fun ω => R0 ω * J ω) =
      (fun ω => Rn ω * J ω + (J ω)^2) := by
    funext ω
    rw [hPath ω]
    ring
  have hProd : Integrable (fun ω => R0 ω * J ω) P := by
    rw [hFun]
    exact hOrth.1.add hJ2
  have hEq : (∫ ω, R0 ω * J ω ∂P) =
      (∫ ω, (J ω)^2 ∂P) := by
    rw [hFun, integral_add hOrth.1 hJ2, hOrth.2, zero_add]
  exact ⟨hJ2, hProd, hEq⟩

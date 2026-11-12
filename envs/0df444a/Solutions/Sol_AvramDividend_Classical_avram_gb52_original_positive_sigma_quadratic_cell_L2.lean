-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb52_original_positive_sigma_quadratic_cell_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:40:23.571521+00:00
-- url     : https://prove2.me/submissions/5409aa5d-25bc-4455-b93e-8b9966a64bef

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb42_bounded_original_gaussian_quadratic_cell
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single physical original Gaussian cell has quadratic-residual
second moment at most eight sigma-fourth times squared cell length. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s Δ : ℝ≥0) :
    let Z : Ω → ℝ := fun ω =>
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    Integrable (fun ω => (Z ω ^ 2 - (Δ : ℝ) * X.σ ^ 2) ^ 2) P ∧
      (∫ ω, (Z ω ^ 2 - (Δ : ℝ) * X.σ ^ 2) ^ 2 ∂P) ≤
        8 * X.σ ^ 4 * (Δ : ℝ) ^ 2 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : Ω → ℝ := fun ω =>
    X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
  change Integrable (fun ω => (Z ω ^ 2 - (Δ : ℝ) * X.σ ^ 2) ^ 2) P ∧
    (∫ ω, (Z ω ^ 2 - (Δ : ℝ) * X.σ ^ 2) ^ 2 ∂P) ≤
      8 * X.σ ^ 4 * (Δ : ℝ) ^ 2
  have hm₁ : Measurable (X.X (s + Δ)) :=
    (X.adapted (s + Δ)).mono (𝓕.le _) le_rfl
  have hm₀ : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le _) le_rfl
  have hmΔ : Measurable (X.X Δ) :=
    (X.adapted Δ).mono (𝓕.le _) le_rfl
  have hZm : Measurable Z :=
    (hm₁.sub hm₀).sub measurable_const
  have hnorm : Measurable (fun ω : Ω =>
      (X.X Δ ω - (Δ : ℝ) * X.c) / X.σ) :=
    (hmΔ.sub measurable_const).div_const _
  have hfourth :
      (∫⁻ ω, ENNReal.ofReal ((Z ω / X.σ) ^ 4) ∂P) ≤
        ENNReal.ofReal (3 * (Δ : ℝ) ^ 2) := by
    have hm : Measurable (fun ω : Ω =>
        (X.X ((s + Δ) - s) ω - (((s + Δ) - s : ℝ≥0) : ℝ) * X.c) /
          X.σ) := by
      simpa only [add_tsub_cancel_left] using hnorm
    have h :=
      avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
        X hν hσ s (s + Δ) (le_add_of_nonneg_right (by positivity)) hm
    simpa only [Z, add_tsub_cancel_left] using h
  have hbound :=
    avram_gb42_bounded_original_gaussian_quadratic_cell
      P (fun _ : Ω => (1 : ℝ)) Z X.σ (Δ : ℝ) 1
      hσ (by norm_num) measurable_const (by intro; norm_num)
      hZm hfourth
  simpa only [one_mul, mul_one, one_pow] using hbound

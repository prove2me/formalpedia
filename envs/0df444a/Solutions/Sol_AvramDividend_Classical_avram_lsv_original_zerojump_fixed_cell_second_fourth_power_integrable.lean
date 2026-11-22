-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_zerojump_fixed_cell_second_fourth_power_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:20:43.197592+00:00
-- url     : https://prove2.me/submissions/c06aa00c-0d2e-4e2d-ba20-1f99d1fb09d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gb52_original_positive_sigma_quadratic_cell_L2
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s Δ : ℝ≥0) :
    let Z : Ω → ℝ := fun ω =>
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    Integrable (fun ω => (Z ω)^2) P ∧
      Integrable (fun ω => (Z ω)^4) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : Ω → ℝ := fun ω =>
    X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
  let c : ℝ := (Δ : ℝ) * X.σ ^ 2
  have hZm : Measurable Z := by
    dsimp [Z]
    exact (((X.adapted (s + Δ)).mono (𝓕.le _) le_rfl).sub
      ((X.adapted s).mono (𝓕.le _) le_rfl)).sub measurable_const
  have hR : Integrable (fun ω => (Z ω ^ 2 - c)^2) P := by
    simpa only [Z, c] using
      (avram_gb52_original_positive_sigma_quadratic_cell_L2
        X hν hσ s Δ).1
  have hBI : Integrable (fun ω => 2 * (Z ω ^ 2 - c)^2 + 2*c^2) P :=
    (hR.const_mul 2).add (integrable_const (2*c^2))
  have hPoint4 (ω : Ω) :
      (Z ω)^4 ≤ 2 * (Z ω ^ 2 - c)^2 + 2*c^2 := by
    nlinarith [sq_nonneg (Z ω ^ 2 - 2*c)]
  have hZ4 : Integrable (fun ω => (Z ω)^4) P := by
    apply hBI.mono' ((hZm.pow_const 4).aestronglyMeasurable)
    exact ae_of_all _ (fun ω => by
      have hn0 : 0 ≤ (Z ω)^4 := by positivity
      have hn1 : 0 ≤ 2 * (Z ω ^ 2 - c)^2 + 2*c^2 := by positivity
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn0, abs_of_nonneg hn1]
        using hPoint4 ω)
  have hZ2 : Integrable (fun ω => (Z ω)^2) P := by
    have hB : Integrable (fun ω => (Z ω)^4 + 1) P :=
      hZ4.add (integrable_const 1)
    apply hB.mono' ((hZm.pow_const 2).aestronglyMeasurable)
    exact ae_of_all _ (fun ω => by
      have hn0 : 0 ≤ (Z ω)^2 := by positivity
      have hn1 : 0 ≤ (Z ω)^4 + 1 := by positivity
      have hP : (Z ω)^2 ≤ (Z ω)^4 + 1 := by
        nlinarith [sq_nonneg (Z ω ^ 2 - (1 / 2 : ℝ))]
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn0, abs_of_nonneg hn1]
        using hP)
  exact ⟨hZ2,hZ4⟩


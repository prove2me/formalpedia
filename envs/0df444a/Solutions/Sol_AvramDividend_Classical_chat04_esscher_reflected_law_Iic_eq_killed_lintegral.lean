-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_reflected_law_Iic_eq_killed_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:42:18.227154+00:00
-- url     : https://prove2.me/submissions/6c1ea7dc-8df1-4ed7-b94b-5c61b0a13b00

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ x : ℝ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))).map (fun ω : Ω => -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) (Iic x) =
    (∫⁻ ω, {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}.indicator (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) := by
  let R : Ω → ℝ := (fun ω : Ω => -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})
  let M : Ω → ℝ≥0∞ := (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
  let S : Set Ω := {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}
  have hR : Measurable R := by
    simpa only [R] using levy_running_infimum_measurable X t
  have hS : MeasurableSet S := by
    simpa only [S] using
      chat04_shifted_lower_survival_measurable_no_schedule X x t
  have hpre : R ⁻¹' Iic x = S := by
    ext ω
    change (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} ≤ x) ↔
      (∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω)
    exact chat04_reflected_infimum_Iic_iff_survival X t ω x
  change ((P.withDensity M).map R) (Iic x) =
    (∫⁻ ω, S.indicator M ω ∂P)
  rw [Measure.map_apply hR measurableSet_Iic, hpre,
      withDensity_apply M hS]
  exact (lintegral_indicator hS M).symm

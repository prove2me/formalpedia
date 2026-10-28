-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_capital_weight_inside_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:16:55.152129+00:00
-- url     : https://prove2.me/submissions/a619acfd-f865-474f-8bf2-33d09282d383

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule

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
    (x : ℝ) (t : ℝ≥0) (β θ : ℝ) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-β * x) *
            Real.exp (θ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
    ENNReal.ofReal (Real.exp (-β * x)) *
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (θ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) := by
  let S : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}
  let m : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X t ω -
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)
  have hS : MeasurableSet S :=
    𝓕.le t _ (shifted_lower_survival_filtration_measurable_no_schedule X x t)
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hm : Measurable (fun ω : Ω => ENNReal.ofReal (m ω)) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((hXt.const_mul θ).sub measurable_const))
  have hf : Measurable
      (S.indicator (fun ω => ENNReal.ofReal (m ω))) :=
    hm.indicator hS
  change (∫⁻ ω, S.indicator
    (fun z => ENNReal.ofReal (Real.exp (-β * x) * m z)) ω ∂P) =
    ENNReal.ofReal (Real.exp (-β * x)) *
      (∫⁻ ω, S.indicator
        (fun z => ENNReal.ofReal (m z)) ω ∂P)
  calc
    (∫⁻ ω, S.indicator
      (fun z => ENNReal.ofReal (Real.exp (-β * x) * m z)) ω ∂P) =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-β * x)) *
        S.indicator (fun z => ENNReal.ofReal (m z)) ω ∂P) := by
      apply lintegral_congr
      intro ω
      by_cases hω : ω ∈ S
      · simp only [Set.indicator_of_mem hω]
        exact ENNReal.ofReal_mul (Real.exp_nonneg _)
      · simp only [Set.indicator_of_notMem hω, mul_zero]
    _ = _ := lintegral_const_mul _ hf

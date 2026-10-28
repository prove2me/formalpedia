-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_killed_survival_real_to_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:11:15.741988+00:00
-- url     : https://prove2.me/submissions/e840e2b0-ea85-4ffc-8a73-2858771d63a4

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
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
    (x : ℝ) (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (θ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
    ENNReal.ofReal (∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by
  let S : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}
  let m : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X t ω -
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)
  have hS : MeasurableSet S :=
    𝓕.le t _ (shifted_lower_survival_filtration_measurable_no_schedule X x t)
  have hI : Integrable (S.indicator m) P :=
    (esscher_exp_process_integrable X θ hθ t).indicator hS
  have hn : ∀ ω : Ω, 0 ≤ S.indicator m ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      exact Real.exp_nonneg _
    · rw [Set.indicator_of_notMem hω]
  change (∫⁻ ω, S.indicator (fun z => ENNReal.ofReal (m z)) ω ∂P) =
    ENNReal.ofReal (∫ ω, S.indicator m ω ∂P)
  calc
    (∫⁻ ω, S.indicator (fun z => ENNReal.ofReal (m z)) ω ∂P) =
        (∫⁻ ω, ENNReal.ofReal (S.indicator m ω) ∂P) := by
      apply lintegral_congr
      intro ω
      by_cases hω : ω ∈ S
      · simp only [Set.indicator_of_mem hω]
      · simp only [Set.indicator_of_notMem hω, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (∫ ω, S.indicator m ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hI
        (Filter.Eventually.of_forall hn)).symm

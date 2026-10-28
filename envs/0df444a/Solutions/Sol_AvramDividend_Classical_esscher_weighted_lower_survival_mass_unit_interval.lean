-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_lower_survival_mass_unit_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:24:18.858165+00:00
-- url     : https://prove2.me/submissions/655511b5-1663-4fee-a607-f7458a2ae6d1

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_martingale
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/--
The mass of paths surviving a lower barrier under a normalised
Esscher exponential lies between zero and one at every horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (t : ℝ≥0) :
    0 ≤
      (∫ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
    ∧
      (∫ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤ 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let f : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X t ω -
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)
  let S : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}
  have hInt : Integrable f P :=
    (esscher_exp_process_martingale X θ hθ).integrable t
  have hs : MeasurableSet S :=
    𝓕.le t _ (shifted_lower_survival_filtration_measurable_no_schedule X x t)
  have hUnit : (∫ ω, f ω ∂P) = 1 := by
    simpa only [f, SpectrallyNegativeLevy.ψ] using
      levy_compensated_exponential_expectation_one X t θ hθ
  have hPos : ∀ ω : Ω, 0 ≤ f ω := by
    intro ω
    exact le_of_lt (Real.exp_pos _)
  change 0 ≤ ∫ ω, S.indicator f ω ∂P ∧
    (∫ ω, S.indicator f ω ∂P) ≤ 1
  constructor
  · apply integral_nonneg
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      exact hPos ω
    · simp [Set.indicator_apply, hω]
  · rw [← hUnit]
    apply integral_mono_ae (hInt.indicator hs) hInt
    filter_upwards [] with ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
    · simp [Set.indicator_apply, hω, hPos ω]

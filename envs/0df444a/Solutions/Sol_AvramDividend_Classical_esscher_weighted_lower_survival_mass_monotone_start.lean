-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_lower_survival_mass_monotone_start
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:18:11.053092+00:00
-- url     : https://prove2.me/submissions/8849d933-9fc4-4764-9bb2-7fc19adb07e5

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_martingale
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/--
For a fixed time horizon, the Esscher-weighted survival mass increases
with the initial reserve because the survival event enlarges.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (x y : ℝ) (hxy : x ≤ y) (t : ℝ≥0) :
    (∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤
    (∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hInt : Integrable (fun ω =>
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) P :=
    (esscher_exp_process_martingale X θ hθ).integrable t
  have hPos : 0 ≤ᵐ[P] (fun ω =>
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) :=
    Filter.Eventually.of_forall (fun ω => le_of_lt (Real.exp_pos _))
  have hsx : MeasurableSet
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} :=
    𝓕.le t _ (shifted_lower_survival_filtration_measurable_no_schedule X x t)
  have hsy : MeasurableSet
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω} :=
    𝓕.le t _ (shifted_lower_survival_filtration_measurable_no_schedule X y t)
  have hIncl :
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} ⊆
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω} := by
    intro ω hω s hs
    have h := hω s hs
    linarith
  rw [integral_indicator hsx, integral_indicator hsy]
  exact setIntegral_mono_set hInt.integrableOn
    (ae_restrict_of_ae hPos) (Filter.Eventually.of_forall hIncl)

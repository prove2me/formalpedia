-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_lower_survival_mass_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:08:06.020985+00:00
-- url     : https://prove2.me/submissions/0be7a1cb-5722-42ad-86e7-c30c9b9f8391

import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_martingale
import Theorems.Thm_AvramDividend_Classical_nonnegative_martingale_survival_mass_antitone
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

open AvramDividend.Classical

/--
The Esscher-weighted probability of survival above a shifted lower barrier
is antitone in the deterministic observation horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ)
    (t u : ℝ≥0) (htu : t ≤ u) :
    (∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X u ω - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤
    (∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hM : Martingale
      (fun (v : ℝ≥0) (ω : Ω) =>
        Real.exp (θ * X.X v ω -
          (v : ℝ) * laplaceExponent X.c X.σ X.ν θ)) 𝓕 P :=
    esscher_exp_process_martingale X θ hθ
  have hPos : ∀ v : ℝ≥0, 0 ≤ᵐ[P]
      (fun ω => Real.exp
        (θ * X.X v ω - (v : ℝ) * laplaceExponent X.c X.σ X.ν θ)) := by
    intro v
    exact Filter.Eventually.of_forall (fun ω => le_of_lt (Real.exp_pos _))
  have hSurv : ∀ v : ℝ≥0, MeasurableSet[𝓕 v]
      {ω : Ω | ∀ s : ℝ≥0, s ≤ v → 0 ≤ x + X.X s ω} := by
    intro v
    exact shifted_lower_survival_filtration_measurable_no_schedule X x v
  have hMono : ∀ v w : ℝ≥0, v ≤ w →
      {ω : Ω | ∀ s : ℝ≥0, s ≤ w → 0 ≤ x + X.X s ω} ⊆
        {ω : Ω | ∀ s : ℝ≥0, s ≤ v → 0 ≤ x + X.X s ω} := by
    intro v w hvw ω hω s hs
    exact hω s (hs.trans hvw)
  exact nonnegative_martingale_survival_mass_antitone
    (fun (v : ℝ≥0) (ω : Ω) =>
      Real.exp (θ * X.X v ω -
        (v : ℝ) * laplaceExponent X.c X.σ X.ν θ))
    hM hPos (fun v => {ω : Ω | ∀ s : ℝ≥0,
      s ≤ v → 0 ≤ x + X.X s ω}) hSurv hMono t u htu

-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_exponential_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:34:53.600875+00:00
-- url     : https://prove2.me/submissions/f351c146-b04c-4141-b430-0b3f57a094a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_adapted
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_levy_compensated_future_increment_condExp_one
import Theorems.Thm_AvramDividend_Classical_levy_compensated_future_increment_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Martingale (fun t ω =>
      Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) 𝓕 P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)
  change Martingale Z 𝓕 P
  constructor
  · intro t
    exact (levy_compensated_exponential_adapted X θ t).stronglyMeasurable
  · intro s t hst
    let f : Ω → ℝ := fun ω =>
      Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)
    let g : Ω → ℝ := fun ω =>
      Real.exp (θ * (X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.ψ θ)
    have hfm : StronglyMeasurable[𝓕 s] f :=
      (levy_compensated_exponential_adapted X θ s).stronglyMeasurable
    have hgm : Integrable g P :=
      levy_compensated_future_increment_integrable X s t hst θ hθ
    have hfactor : (fun ω => f ω * g ω) = Z t := by
      funext ω
      dsimp [f, g, Z]
      rw [← Real.exp_add, NNReal.coe_sub hst]
      congr 1
      ring
    have hproduct : Integrable (fun ω => f ω * g ω) P := by
      rw [hfactor]
      exact levy_compensated_exponential_integrable X t θ hθ
    have hfuture : P[g | 𝓕 s] =ᵐ[P] (fun _ => (1 : ℝ)) := by
      exact levy_compensated_future_increment_condExp_one X s t hst θ hθ
    have hpull :=
      condExp_mul_of_aestronglyMeasurable_left
        hfm.aestronglyMeasurable hproduct hgm
    change P[(fun ω => f ω * g ω) | 𝓕 s] =ᵐ[P]
      (fun ω => f ω * P[g | 𝓕 s] ω) at hpull
    have hcombined :
        P[(fun ω => f ω * g ω) | 𝓕 s] =ᵐ[P] f := by
      filter_upwards [hpull, hfuture] with ω hp hfut
      simpa only [hfut, mul_one] using hp
    rw [hfactor] at hcombined
    exact hcombined

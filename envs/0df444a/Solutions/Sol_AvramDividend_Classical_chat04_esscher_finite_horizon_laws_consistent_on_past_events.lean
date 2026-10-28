-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_finite_horizon_laws_consistent_on_past_events
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:40:40.358353+00:00
-- url     : https://prove2.me/submissions/bc38cd73-3a72-4eb0-b115-6bcc77780f91

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_chat01_levy_exponential_early_event_integral_eq
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)))) A =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))) A := by
  haveI : IsProbabilityMeasure P := X.isProbability
  have hAm : MeasurableSet A := 𝓕.le s _ hA
  have key := AvramDividend.Classical.chat01_levy_exponential_early_event_integral_eq X θ hθ s t hst A hA
  rw [withDensity_apply _ hAm, withDensity_apply _ hAm,
    ← ofReal_integral_eq_lintegral_ofReal
      ((AvramDividend.Classical.esscher_exp_process_integrable X θ hθ s).integrableOn)
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
    ← ofReal_integral_eq_lintegral_ofReal
      ((AvramDividend.Classical.esscher_exp_process_integrable X θ hθ t).integrableOn)
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)), key]

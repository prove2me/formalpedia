-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_past_event_setIntegral_consistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:14:01.753204+00:00
-- url     : https://prove2.me/submissions/47f99d77-5bdd-4e4e-bcc3-a98bec27abc5

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_setIntegral_eq_of_ambient_measures_agree_on_subsigma
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
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
    (θ : ℝ) (hθ : 0 ≤ θ) (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (f : Ω → ℝ) (hf : StronglyMeasurable[𝓕 s] f) :
    (∫ ω in A, f ω ∂(P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))) =
    (∫ ω in A, f ω ∂(P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) := by
  apply setIntegral_eq_of_ambient_measures_agree_on_subsigma (𝓕.le s)
    _ _ ?_ A hA f hf
  intro B hB
  simpa only [SpectrallyNegativeLevy.ψ] using
    chat04_esscher_finite_horizon_laws_consistent_on_past_events
      X θ hθ s t hst B hB

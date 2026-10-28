-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_future_extracted_poisson_marked_compensation_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:34:06.541423+00:00
-- url     : https://prove2.me/submissions/292e0788-902a-4dd5-a4aa-4b45c43a6b60

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_levy_future_path_measurable_jump_extractor_indep_past_ws01b
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- Actual-Lévy one-step jump compensation from a measurable future-path
Poisson count/marks representation, without any independent-past premise. -/
theorem solution
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (hHi : Integrable H P)
    (J : (ℝ≥0 → ℝ) → (ℕ × (ℕ → E))) (hJ : Measurable J)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hRep : ∀ ω, J (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) =
        (K ω, fun n : ℕ => Y n ω))
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) P)
    (hYm : ∀ n, Measurable (Y n))
    (ν : Measure E) (hYL : ∀ n, HasLaw (Y n) ν P)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) P)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν) :
    (∫ ω, H ω * (∑ n ∈ Finset.range (K ω), f (Y n ω)) ∂P) =
      (∫ ω, H ω ∂P) * ((r : ℝ) * ∫ y, f y ∂ν) := by
  have hHm : Measurable H :=
    hH.mono (𝓕.le s) le_rfl
  have hPast : IndepFun H
      (fun ω => (K ω, fun n : ℕ => Y n ω)) P := by
    have hJindep :=
      levy_future_path_measurable_jump_extractor_indep_past_ws01b
        X s H hH J hJ
    have heq : (fun ω => J
        (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) =
        (fun ω => (K ω, fun n : ℕ => Y n ω)) := by
      funext ω
      exact hRep ω
    rwa [heq] at hJindep
  exact poisson_predictable_marked_compensation_closed_ws01b
    P ν H hHm hHi K Y hKm r hKlaw hYm hYL
    hCountMarks hPast f hf hfI

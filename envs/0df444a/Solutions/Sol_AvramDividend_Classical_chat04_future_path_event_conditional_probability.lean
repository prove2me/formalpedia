-- Prove2me | solution 1 for AvramDividend.Classical.chat04_future_path_event_conditional_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:19:52.260504+00:00
-- url     : https://prove2.me/submissions/821b03a4-5908-45b7-91b9-993863b7cbb3

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_whole_future_process_indep_past_of_finite_cylinders
import Theorems.Thm_AvramDividend_Classical_chat04_full_shifted_future_path_condExp_of_independence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

attribute [local instance] Classical.propDecidable

/-!
Full shifted future-path event is conditionally independent of F_s,
given joint finite-cylinder independence. The event may depend on ALL
future times. Its 0/1 real indicator is automatically integrable because
the canonical Levy law is a probability measure. This supports killed
future-interval survival events represented by measurable path subsets.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (hFinite : ∀ I : Finset ℝ≥0,
      Indep (⨆ t ∈ I, MeasurableSpace.comap
        (fun ω => X.X (s + t) ω - X.X s ω) inferInstance)
        (𝓕 s) P)
    (G : Set (ℝ≥0 → ℝ)) (hG : MeasurableSet G) :
    P[(fun ω => if (fun t => X.X (s + t) ω - X.X s ω) ∈ G
        then (1 : ℝ) else 0) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, (if (fun t => X.X (s + t) ω - X.X s ω) ∈ G
        then (1 : ℝ) else 0) ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (s + t) ω - X.X s ω
  let f : (ℝ≥0 → ℝ) → ℝ :=
    fun y => if y ∈ G then 1 else 0
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro t
    have ht : Measurable (X.X (s + t)) :=
      (X.adapted (s + t)).mono (𝓕.le (s + t)) le_rfl
    have hs : Measurable (X.X s) :=
      (X.adapted s).mono (𝓕.le s) le_rfl
    exact ht.sub hs
  have hf : Measurable f := by
    dsimp [f]
    exact Measurable.ite hG measurable_const measurable_const
  have hA : MeasurableSet (Y ⁻¹' G) := hG.preimage hY
  have hInt : Integrable (fun ω => f (Y ω)) P := by
    have hEq : (fun ω : Ω => f (Y ω)) =
        ((Y ⁻¹' G).indicator (fun _ : Ω => (1 : ℝ))) := by
      funext ω
      by_cases h : Y ω ∈ G
      · simp [f, Set.indicator, h]
      · simp [f, Set.indicator, h]
    rw [hEq]
    exact (integrable_const (1 : ℝ)).indicator hA
  have hFuture :=
    AvramDividend.Classical.chat04_whole_future_process_indep_past_of_finite_cylinders
      X s hFinite
  have hCE :=
    AvramDividend.Classical.chat04_full_shifted_future_path_condExp_of_independence
      X s hFuture f hf hInt
  simpa only [f, Y] using hCE

-- Prove2me | solution 1 for AvramDividend.Classical.chat04_countable_two_sided_killed_scale_markov_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:58:45.191851+00:00
-- url     : https://prove2.me/submissions/8b8c7b26-f858-4e5f-95de-fa7ae807c78a

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_unconditional_history_future_path_markov_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_countable_two_sided_killed_scale_payoff_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

/-- Independent Lévy future paths factorise a countably two-sided killed reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (τ : ℕ → ℝ≥0) (T t : ℝ≥0)
    (a q : ℝ) (W : ℝ → ℝ) (hW : Measurable W) :
    (∫⁻ ω,
      if ∀ j : ℕ, τ j ≤ T →
        0 ≤ H ω + (X.X (s + τ j) ω - X.X s ω) ∧
        H ω + (X.X (s + τ j) ω - X.X s ω) ≤ a
      then ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) *
          W (H ω + (X.X (s + t) ω - X.X s ω)))
      else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ h, ∫⁻ y,
      (if ∀ j : ℕ, τ j ≤ T →
        0 ≤ h + y (τ j) ∧ h + y (τ j) ≤ a
       then ENNReal.ofReal
         (Real.exp (-(q * (t : ℝ))) * W (h + y t))
       else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)
      ∂(Measure.map H P) := by
  let f : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞ := fun z =>
    if ∀ j : ℕ, τ j ≤ T →
      0 ≤ z.1 + z.2 (τ j) ∧ z.1 + z.2 (τ j) ≤ a
    then ENNReal.ofReal
      (Real.exp (-(q * (t : ℝ))) * W (z.1 + z.2 t))
    else 0
  have hf : Measurable f :=
    chat04_countable_two_sided_killed_scale_payoff_measurable τ T t a q W hW
  simpa only [f] using
    (chat04_unconditional_history_future_path_markov_tonelli X s H hH f hf)

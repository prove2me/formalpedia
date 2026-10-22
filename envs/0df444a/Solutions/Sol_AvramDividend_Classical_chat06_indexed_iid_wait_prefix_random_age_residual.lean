-- Prove2me | solution 1 for AvramDividend.Classical.chat06_indexed_iid_wait_prefix_random_age_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:06:58.100369+00:00
-- url     : https://prove2.me/submissions/990373f9-fec0-4cad-a2e9-b8cbb2eed895

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_masked_iid_prefix_full_suffix_independence
import Theorems.Thm_AvramDividend_Classical_chat06_independent_past_event_exponential_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- At each deterministic renewal index n, the complete masked waiting
prefix is independent of the next wait. Thus any measurable prefix
event obeys exact random-age exponential residual memorylessness. -/
theorem indexed_iid_wait_prefix_random_age_residual
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (Z : Ω → (ℕ → ℝ))
    (hZ : Z = fun ω i => if h : i < n then τ i ω else 0)
    (age : (ℕ → ℝ) → ℝ) (hAge : Measurable age)
    (D : Set (ℕ → ℝ)) (hD : MeasurableSet D)
    (hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ n ω} =
      P {ω | Z ω ∈ D ∧ age (Z ω) < τ n ω} *
        ENNReal.ofReal (Real.exp (-t)) := by
  have hZMeas : Measurable Z := by
    rw [hZ]
    apply measurable_pi_lambda
    intro i
    by_cases hi : i < n
    · simpa [hi] using hτ i
    · simp [hi]
  have hInd : IndepFun Z (τ n) P := by
    have hSuffix :=
      AvramDividend.Classical.chat06_masked_iid_prefix_full_suffix_independence
        τ hτ hiid n
    have h0 := hSuffix.comp measurable_id
      (measurable_pi_apply (0 : ℕ))
    rw [hZ]
    simpa [Function.comp_def] using h0
  exact
    AvramDividend.Classical.chat06_independent_past_event_exponential_residual
      Z (τ n) age hZMeas (hτ n) hAge hInd D hD
      hNonneg hTail t ht

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (Z : Ω → (ℕ → ℝ))
    (hZ : Z = fun ω i => if h : i < n then τ i ω else 0)
    (age : (ℕ → ℝ) → ℝ) (hAge : Measurable age)
    (D : Set (ℕ → ℝ)) (hD : MeasurableSet D)
    (hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ n ω} =
      P {ω | Z ω ∈ D ∧ age (Z ω) < τ n ω} *
        ENNReal.ofReal (Real.exp (-t)) := by
  exact indexed_iid_wait_prefix_random_age_residual
    τ hτ hiid n Z hZ age hAge D hD hNonneg hTail t ht

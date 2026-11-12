-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_renewal_residual_future_from_ae_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:37:21.56688+00:00
-- url     : https://prove2.me/submissions/d1e06965-2c84-4560-a7e4-773a3bfdee09

import Mathlib.Probability.HasLaw
import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_iid_random_count_residual_full_future_joint
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- An almost-sure exact count identity suffices for the random-count renewal law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (hN : Measurable (fun ω => N ω clock))
    (t : ℝ) (ht : 0 ≤ t)
    (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n,
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | t < τ (N ω clock) ω -
      (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
        ENNReal.ofReal (Real.exp (-t)) * μ B := by
  have hCount (n : ℕ) :
      (fun ω : Ω => N ω clock = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω) := by
    filter_upwards [hThreshold] with ω hω
    exact propext
      (AvramDividend.Classical.chat06_exact_count_cylinder_from_arrival_threshold
        (fun i => τ i ω) (N ω) (hω) clock hclock n)
  exact
    AvramDividend.Classical.chat06_iid_random_count_residual_full_future_joint
      τ hτ hiid (fun ω => N ω clock) hN clock t ht
      μ hLaw B hB hTail hCount
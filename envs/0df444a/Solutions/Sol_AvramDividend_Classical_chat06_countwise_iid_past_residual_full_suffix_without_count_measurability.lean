-- Prove2me | solution 1 for AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_without_count_measurability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:48:36.392421+00:00
-- url     : https://prove2.me/submissions/49c3bd5b-76c1-4b7e-ae2e-a6b58494a36c

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_iid_past_residual_full_suffix_from_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_count_measurable_from_arrival_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Derive count measurability from the arrival threshold relation
before applying the accepted countwise past/future factorisation. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (H : Set Ω) (hH : MeasurableSet H)
    (hRep : ∀ n : ℕ, ∃ Q : Set (ℕ → ℝ),
      MeasurableSet Q ∧
      (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
        (fun ω : Ω =>
          (fun i : ℕ => if i < n then τ i ω else 0) ∈ Q ∧
          N ω clock = n))
    (t : ℝ) (ht : 0 ≤ t) (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n, HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | ω ∈ H ∧
      t < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
      (P H * ENNReal.ofReal (Real.exp (-t))) * μ B := by
  exact AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_from_threshold
    τ hτ hiid N hThreshold clock hclock
    (AvramDividend.Classical.chat06_count_measurable_from_arrival_threshold
      τ hτ N hThreshold clock)
    H hH hRep t ht μ hLaw B hB hTail

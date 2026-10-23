-- Prove2me | solution 1 for AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_common_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:48:31.862366+00:00
-- url     : https://prove2.me/submissions/2111e75c-d60d-4a72-b490-f702c7198e11

import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_iid_past_residual_full_suffix_from_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_iid_shifted_suffix_common_infinite_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal

/-- An IID common marginal law determines the full future suffix law,
so countwise past-event representation yields the residual/future
joint product identity without an extra suffix-law hypothesis. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (ν : Measure ℝ) (hν : ∀ i, HasLaw (τ i) ν P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (hN : Measurable (fun ω => N ω clock))
    (H : Set Ω) (hH : MeasurableSet H)
    (hRep : ∀ n : ℕ, ∃ Q : Set (ℕ → ℝ),
      MeasurableSet Q ∧
      (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
        (fun ω : Ω =>
          (fun i : ℕ => if i < n then τ i ω else 0) ∈ Q ∧
          N ω clock = n))
    (t : ℝ) (ht : 0 ≤ t)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | ω ∈ H ∧
      t < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
      (P H * ENNReal.ofReal (Real.exp (-t))) *
        infinitePi (fun _ : ℕ => ν) B := by
  exact AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_from_threshold
    τ hτ hiid N hThreshold clock hclock hN H hH hRep
    t ht (infinitePi (fun _ : ℕ => ν))
    (fun n =>
      AvramDividend.Classical.chat06_iid_shifted_suffix_common_infinite_product_law
        τ hτ hiid ν hν n)
    B hB hTail

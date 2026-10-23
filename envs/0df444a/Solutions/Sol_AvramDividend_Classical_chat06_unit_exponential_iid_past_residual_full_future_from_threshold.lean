-- Prove2me | solution 1 for AvramDividend.Classical.chat06_unit_exponential_iid_past_residual_full_future_from_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:07:24.704492+00:00
-- url     : https://prove2.me/submissions/c3f22a86-8009-4e17-86ed-5a793dec3bba

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_iid_past_residual_full_suffix_common_law
import Theorems.Thm_AvramDividend_Classical_chat06_count_measurable_from_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_haslaw_survival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal

/-- IID unit-exponential interarrivals automatically supply the
renewal count measurability, full suffix product law, and tail law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hExp : ∀ i, HasLaw (τ i) (expMeasure 1) P)
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
    (t : ℝ) (ht : 0 ≤ t)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    P {ω | ω ∈ H ∧
      t < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
      (P H * ENNReal.ofReal (Real.exp (-t))) *
        infinitePi (fun _ : ℕ => expMeasure 1) B := by
  exact AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_common_law
    τ hτ hiid (expMeasure 1) hExp N hThreshold clock hclock
    (AvramDividend.Classical.chat06_count_measurable_from_arrival_threshold
      τ hτ N hThreshold clock)
    H hH hRep t ht B hB
    (fun n u hu =>
      AvramDividend.Classical.chat06_unit_exponential_haslaw_survival
        (τ n) (hExp n) u hu)

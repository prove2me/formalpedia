-- Prove2me | solution 1 for AvramDividend.Classical.chat06_random_count_residual_full_future_joint_from_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T06:42:31.776988+00:00
-- url     : https://prove2.me/submissions/a5b124d4-002f-4557-ba4d-03327351da0c

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_iid_random_count_residual_full_future_joint

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The random-count exponential residual and complete future wait suffix
have their product law under the exact renewal arrival-threshold property. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
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
    apply Filter.Eventually.of_forall
    intro ω
    exact propext
      (AvramDividend.Classical.chat06_exact_count_cylinder_from_arrival_threshold
        (fun i => τ i ω) (N ω) (hThreshold ω) clock hclock n)
  exact
    AvramDividend.Classical.chat06_iid_random_count_residual_full_future_joint
      τ hτ hiid (fun ω => N ω clock) hN clock t ht
      μ hLaw B hB hTail hCount

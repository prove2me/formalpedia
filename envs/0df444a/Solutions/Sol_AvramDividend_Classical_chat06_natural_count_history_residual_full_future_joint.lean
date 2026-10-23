-- Prove2me | solution 1 for AvramDividend.Classical.chat06_natural_count_history_residual_full_future_joint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:07:20.533128+00:00
-- url     : https://prove2.me/submissions/d69014c8-2356-43e6-8c23-e5f1338e7aab

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_natural_history_count_cylinder_prefix_representation
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_iid_past_residual_full_suffix_from_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The full observed counting history through a deterministic horizon
factors jointly from the remaining exponential wait and the complete
future waiting-time suffix, using measurable finite-prefix reconstruction. -/
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
    (H : Set Ω) (hH : MeasurableSet H)
    (hHpast : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H)
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
  have hRep (n : ℕ) :
      ∃ Q : Set (ℕ → ℝ), MeasurableSet Q ∧
        (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
          (fun ω : Ω =>
            (fun i : ℕ => if i < n then τ i ω else 0) ∈ Q ∧
            N ω clock = n) := by
    exact AvramDividend.Classical.chat06_natural_history_count_cylinder_prefix_representation
      P (fun ω i => τ i ω)
      (fun ω i => if i < n then τ i ω else 0)
      N clock n hThreshold (by intro ω i; rfl) H hHpast
  exact AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_from_threshold
    τ hτ hiid N hThreshold clock hclock hN H hH hRep
    t ht μ hLaw B hB hTail

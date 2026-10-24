-- Prove2me | solution 1 for AvramDividend.Classical.chat06_unit_exponential_full_count_history_independent_future_suffix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:33:22.984483+00:00
-- url     : https://prove2.me/submissions/a3c2fc80-cdfc-45b1-8e1e-9ec9c78b7726

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_natural_history_count_cylinder_prefix_representation
import Theorems.Thm_AvramDividend_Classical_chat06_observed_count_history_measurable_from_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_iid_past_residual_full_future_from_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal

/-- The complete past counting path is independent of residual
exponential survival together with every measurable event of the
infinite sequence of future waiting times. -/
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
    (H : Set Ω)
    (hHpast : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H)
    (t : ℝ) (ht : 0 ≤ t)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    P {ω | ω ∈ H ∧
      t < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
      (P H * ENNReal.ofReal (Real.exp (-t))) *
        infinitePi (fun _ : ℕ => expMeasure 1) B := by
  have hPath : Measurable
      (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ)) :=
    AvramDividend.Classical.chat06_observed_count_history_measurable_from_arrival_threshold
      τ hτ N hThreshold clock
  obtain ⟨C, hC, hPre⟩ := (MeasurableSpace.measurableSet_comap).mp hHpast
  have hH : MeasurableSet H := by
    rw [← hPre]
    exact hPath hC
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
  exact AvramDividend.Classical.chat06_unit_exponential_iid_past_residual_full_future_from_threshold
    τ hτ hiid hExp N hThreshold clock hclock H hH hRep t ht B hB

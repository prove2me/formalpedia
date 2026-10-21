-- Prove2me | solution 1 for AvramDividend.Classical.chat06_positive_count_finite_prefix_measurable_with_defs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:17:17.192302+00:00
-- url     : https://prove2.me/submissions/507fd60b-3bf1-4560-b006-8051d2246f08

import Definitions.Def_AvramChat06_FiniteWaitPrefixCylinder
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Fin.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

namespace AvramChat06

/-- Turn a finite waiting-time prefix into an infinite real
sequence by padding everything beyond its last coordinate with zero. -/
private theorem measurable_padWaitPrefix
    (n i : ℕ) :
    Measurable (fun g : Fin (n + 2) → ℝ => padWaitPrefix n g i) := by
  by_cases hi : i < n + 2
  · simpa [padWaitPrefix, hi] using
      (measurable_pi_apply (⟨i, hi⟩ : Fin (n + 2)))
  · simp [padWaitPrefix, hi]

/-- The event can be observed from the first n+2 waiting times. -/
theorem positiveCountPrefixEvent_measurable (n : ℕ) (t : ℝ) :
    MeasurableSet (positiveCountPrefixEvent n t) := by
  have hm (k : ℕ) :
      Measurable (fun g : Fin (n + 2) → ℝ =>
        ∑ j ∈ Finset.range k, padWaitPrefix n g j) :=
    Finset.measurable_sum _ fun j _ => measurable_padWaitPrefix n j
  exact (hm (n + 1) measurableSet_Iic).inter
    (hm (n + 2) measurableSet_Ioi)

/-- A concrete pair of arrival-time inequalities depends only on
the finite observed prefix, not on unobserved future waits. -/
theorem arrival_pair_eq_prefixEvent
    {Ω : Type*} (τ : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) :
    {ω | (∑ j ∈ Finset.range (n + 1), τ j ω) ≤ t ∧
       t < ∑ j ∈ Finset.range (n + 2), τ j ω} =
      (fun ω (i : Fin (n + 2)) => τ i ω) ⁻¹'
        positiveCountPrefixEvent n t := by
  have hsum (k : ℕ) (hk : k ≤ n + 2) (ω : Ω) :
      (∑ j ∈ Finset.range k,
        padWaitPrefix n (fun i : Fin (n + 2) => τ i ω) j) =
      ∑ j ∈ Finset.range k, τ j ω := by
    apply Finset.sum_congr rfl
    intro j hj
    have hlt : j < n + 2 :=
      lt_of_lt_of_le (Finset.mem_range.mp hj) hk
    simp [padWaitPrefix, hlt]
  ext ω
  change ((∑ j ∈ Finset.range (n + 1), τ j ω) ≤ t ∧
       t < ∑ j ∈ Finset.range (n + 2), τ j ω) ↔
    ((∑ j ∈ Finset.range (n + 1),
        padWaitPrefix n (fun i : Fin (n + 2) => τ i ω) j) ≤ t ∧
     t < ∑ j ∈ Finset.range (n + 2),
        padWaitPrefix n (fun i : Fin (n + 2) => τ i ω) j)
  rw [hsum (n + 1) (Nat.le_succ (n + 1)) ω, hsum (n + 2) le_rfl ω]

end AvramChat06

open AvramChat06

theorem solution (n : ℕ) (t : ℝ) :
    MeasurableSet (positiveCountPrefixEvent n t) := by
  exact positiveCountPrefixEvent_measurable n t

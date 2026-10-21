-- Prove2me | solution 1 for AvramDividend.Classical.chat06_positive_count_masked_past_observable_with_defs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:17:43.215676+00:00
-- url     : https://prove2.me/submissions/102b76e7-02fd-46ee-82ac-1a9a67a30e92

import Definitions.Def_AvramChat06_MaskedWaitPrefixCylinder
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Order.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

namespace AvramChat06

/-- A fixed-codomain, sequence-valued observation of only the
first k exponential waiting times. Later coordinates are zero. -/
theorem positiveCountPastCylinder_measurable (n : ℕ) (t : ℝ) :
    MeasurableSet (positiveCountPastCylinder n t) := by
  have hs (k : ℕ) :
      Measurable (fun g : ℕ → ℝ =>
        ∑ i ∈ Finset.range k, g i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  exact (hs (n + 1) measurableSet_Iic).inter
    (hs (n + 2) measurableSet_Ioi)

/-- An almost-sure arrival-cylinder identity for a positive count
is precisely an almost-sure preimage of a measurable set in the
*observed finite prefix*, padded to the constant codomain ℕ→ℝ.
The predicate may fail outside the full-measure good-path event. -/
theorem positive_count_event_is_ae_masked_past
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℕ) (n : ℕ) (t : ℝ)
    (hAE : (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (∑ i ∈ Finset.range (n + 1), τ i ω) ≤ t ∧
        t < ∑ i ∈ Finset.range (n + 2), τ i ω)) :
    ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
        (fun ω : Ω => maskedWaitPrefix τ (n + 2) ω ∈ S) := by
  refine ⟨positiveCountPastCylinder n t,
    positiveCountPastCylinder_measurable n t, ?_⟩
  have hsum (k : ℕ) (hk : k ≤ n + 2) (ω : Ω) :
      (∑ i ∈ Finset.range k, maskedWaitPrefix τ (n + 2) ω i) =
        ∑ i ∈ Finset.range k, τ i ω := by
    apply Finset.sum_congr rfl
    intro i hi
    have hlt : i < n + 2 :=
      lt_of_lt_of_le (Finset.mem_range.mp hi) hk
    simp [maskedWaitPrefix, hlt]
  filter_upwards [hAE] with ω hω
  apply propext
  have hp :
      ((∑ i ∈ Finset.range (n + 1), τ i ω) ≤ t ∧
        t < ∑ i ∈ Finset.range (n + 2), τ i ω) ↔
       maskedWaitPrefix τ (n + 2) ω ∈
         positiveCountPastCylinder n t := by
    change ((∑ i ∈ Finset.range (n + 1), τ i ω) ≤ t ∧
      t < ∑ i ∈ Finset.range (n + 2), τ i ω) ↔
      ((∑ i ∈ Finset.range (n + 1),
        maskedWaitPrefix τ (n + 2) ω i) ≤ t ∧
       t < ∑ i ∈ Finset.range (n + 2),
         maskedWaitPrefix τ (n + 2) ω i)
    rw [hsum (n + 1) (Nat.le_succ (n + 1)) ω,
      hsum (n + 2) le_rfl ω]
  exact (Iff.of_eq hω).trans hp

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℕ) (n : ℕ) (t : ℝ)
    (hAE : (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (∑ i ∈ Finset.range (n + 1), τ i ω) ≤ t ∧
        t < ∑ i ∈ Finset.range (n + 2), τ i ω)) :
    ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
        (fun ω : Ω => maskedWaitPrefix τ (n + 2) ω ∈ S) := by
  exact positive_count_event_is_ae_masked_past τ N n t hAE

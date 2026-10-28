-- Prove2me | solution 1 for AvramDividend.Classical.chat06_positive_count_masked_past_observable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:39:31.423329+00:00
-- url     : https://prove2.me/submissions/5372e55e-3d40-4e86-85dd-c61357e65398

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Order.Basic

open MeasureTheory Set
namespace AvramChat06M

def maskedWaitPrefix {Ω : Type*}
    (τ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) (i : ℕ) : ℝ :=
  if i < k then τ i ω else 0

end AvramChat06M

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℕ) (n : ℕ) (t : ℝ)
    (hAE : (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (∑ i ∈ Finset.range (n + 1), τ i ω) ≤ t ∧
        t < ∑ i ∈ Finset.range (n + 2), τ i ω)) :
    ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
        (fun ω : Ω => AvramChat06M.maskedWaitPrefix τ (n + 2) ω ∈ S) := by
  refine ⟨{x | (∑ i ∈ Finset.range (n + 1), x i) ≤ t ∧ t < ∑ i ∈ Finset.range (n + 2), x i},
    ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
        measurable_const
    · exact measurableSet_lt measurable_const
        (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  · refine hAE.trans (Filter.Eventually.of_forall fun ω => ?_)
    have h1 : ∑ i ∈ Finset.range (n + 1), AvramChat06M.maskedWaitPrefix τ (n + 2) ω i
        = ∑ i ∈ Finset.range (n + 1), τ i ω :=
      Finset.sum_congr rfl fun i hi => by
        simp only [Finset.mem_range] at hi
        simp [AvramChat06M.maskedWaitPrefix, show i < n + 2 by omega]
    have h2 : ∑ i ∈ Finset.range (n + 2), AvramChat06M.maskedWaitPrefix τ (n + 2) ω i
        = ∑ i ∈ Finset.range (n + 2), τ i ω :=
      Finset.sum_congr rfl fun i hi => by
        simp only [Finset.mem_range] at hi
        simp [AvramChat06M.maskedWaitPrefix, hi]
    simp only [mem_setOf_eq, h1, h2]

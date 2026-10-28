-- Prove2me | solution 1 for AvramDividend.Classical.bv_cauchyseq_real_event_measurable_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:20:28.089783+00:00
-- url     : https://prove2.me/submissions/c2d56ea1-dd0e-4120-873f-5e5a6a3564b6

import Mathlib
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set

theorem solution
    {E : Type*} [MeasurableSpace E]
    (v : ℕ → E → ℝ) (hv : ∀ n, Measurable (v n)) :
    MeasurableSet {e : E | CauchySeq (fun n => v n e)} := by
  classical
  let C : Set E :=
    ⋂ k : ℕ, ⋃ N : ℕ, ⋂ m : ℕ, ⋂ n : ℕ,
      {e | N ≤ m → N ≤ n →
        |v m e - v n e| ≤ (1 : ℝ) / ((k : ℝ) + 1)}
  have hC : MeasurableSet C := by
    dsimp [C]
    refine MeasurableSet.iInter (fun k => ?_)
    refine MeasurableSet.iUnion (fun N => ?_)
    refine MeasurableSet.iInter (fun m => ?_)
    refine MeasurableSet.iInter (fun n => ?_)
    by_cases hm : N ≤ m
    · by_cases hn : N ≤ n
      · simpa [hm, hn] using
          (measurableSet_le (((hv m).sub (hv n)).abs)
            (measurable_const :
              Measurable (fun _ : E =>
                (1 : ℝ) / ((k : ℝ) + 1))))
      · simp [hn]
    · simp [hm]
  have hIff (e : E) :
      e ∈ C ↔ CauchySeq (fun n => v n e) := by
    simp only [C, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro h
      apply Metric.cauchySeq_iff.mpr
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h k
      refine ⟨N, ?_⟩
      intro m hm n hn
      have hmn := hN m n hm hn
      simpa only [Real.dist_eq] using (lt_of_le_of_lt hmn hk)
    · intro hc k
      have hε : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
      obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hc) _ hε
      refine ⟨N, ?_⟩
      intro m n hm hn
      have hmn := hN m hm n hn
      simpa only [Real.dist_eq] using (le_of_lt hmn)
  have hEq : {e : E | CauchySeq (fun n => v n e)} = C := by
    ext e
    exact (hIff e).symm
  rw [hEq]
  exact hC

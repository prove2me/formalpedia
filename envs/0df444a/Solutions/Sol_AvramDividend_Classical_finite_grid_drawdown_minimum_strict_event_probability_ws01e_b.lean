-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_drawdown_minimum_strict_event_probability_ws01e_b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:08:49.21211+00:00
-- url     : https://prove2.me/submissions/e47884a1-8855-47da-ba35-5ad1bc5157fb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b

set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

open MeasureTheory AvramDividend.Classical

/-- Finite-grid strict drawdown and strict minimum events agree in a reversal-invariant law. -/
theorem solution (n : ℕ) (μ : Measure (ℕ → ℝ)) (a : ℝ)
    (hrev : Measure.map
      (fun v : ℕ → ℝ => fun j : ℕ =>
        if j < n then v (n - 1 - j) else v j) μ = μ) :
    μ {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) v -
        Finset.sum (Finset.range k.val) v < a} =
    μ {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) v < a} := by
  let rev : (ℕ → ℝ) → (ℕ → ℝ) :=
    fun v j => if j < n then v (n - 1 - j) else v j
  let prefSum : (ℕ → ℝ) → Fin n.succ → ℝ :=
    fun v k => Finset.sum (Finset.range k.val) v
  change μ {v | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) v - prefSum v k < a} =
    μ {v | ∃ k : Fin n.succ, prefSum v k < a}
  have hsum (v : ℕ → ℝ) (k : Fin n.succ) :
      prefSum (rev v) k =
        Finset.sum (Finset.range k.val) (fun j => v (n - 1 - j)) := by
    dsimp [prefSum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj)
      (Nat.lt_succ_iff.mp k.isLt)
    simp only [rev, if_pos hjlt]
  have hpath (v : ℕ → ℝ) :
      (∃ k : Fin n.succ,
        Finset.sum (Finset.range n) v - prefSum v k < a) ↔
      (∃ k : Fin n.succ, prefSum (rev v) k < a) := by
    have hR := finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b v n
    constructor
    · rintro ⟨k, hk⟩
      have hmem :
          Finset.sum (Finset.range n) v - prefSum v k ∈
          Set.range (fun l : Fin n.succ =>
            Finset.sum (Finset.range l.val) (fun j => v (n - 1 - j))) := by
        rw [← hR]
        exact ⟨k, rfl⟩
      obtain ⟨l, hl⟩ := hmem
      change Finset.sum (Finset.range l.val) (fun j => v (n - 1 - j)) =
        Finset.sum (Finset.range n) v - prefSum v k at hl
      refine ⟨l, ?_⟩
      rw [hsum v l, hl]
      exact hk
    · rintro ⟨k, hk⟩
      have hmem :
          Finset.sum (Finset.range k.val) (fun j => v (n - 1 - j)) ∈
          Set.range (fun l : Fin n.succ =>
            Finset.sum (Finset.range n) v -
              Finset.sum (Finset.range l.val) v) := by
        rw [hR]
        exact ⟨k, rfl⟩
      obtain ⟨l, hl⟩ := hmem
      change Finset.sum (Finset.range n) v - prefSum v l =
        Finset.sum (Finset.range k.val) (fun j => v (n - 1 - j)) at hl
      refine ⟨l, ?_⟩
      change Finset.sum (Finset.range n) v - prefSum v l < a
      rw [hl, ← hsum v k]
      exact hk
  have hPrefix (k : Fin n.succ) :
      Measurable (fun v : ℕ → ℝ => prefSum v k) := by
    change Measurable (fun v : ℕ → ℝ =>
      Finset.sum (Finset.range k.val) (fun j => v j))
    exact Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)
  have hEvent : MeasurableSet
      {v : ℕ → ℝ | ∃ k : Fin n.succ, prefSum v k < a} := by
    have hUnion : MeasurableSet (⋃ k : Fin n.succ,
        {v : ℕ → ℝ | prefSum v k < a}) :=
      MeasurableSet.iUnion (fun k =>
        measurableSet_lt (hPrefix k) measurable_const)
    simpa only [Set.setOf_exists] using hUnion
  have hRevMeas : Measurable rev := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j < n
    · simpa only [rev, if_pos hj] using
        (measurable_pi_apply (n - 1 - j) :
          Measurable (fun v : ℕ → ℝ => v (n - 1 - j)))
    · simpa only [rev, if_neg hj] using
        (measurable_pi_apply j :
          Measurable (fun v : ℕ → ℝ => v j))
  change Measure.map rev μ = μ at hrev
  calc
    μ {v | ∃ k : Fin n.succ,
        Finset.sum (Finset.range n) v - prefSum v k < a} =
      μ (rev ⁻¹' {v | ∃ k : Fin n.succ, prefSum v k < a}) := by
        congr 1
        ext v
        exact hpath v
    _ = Measure.map rev μ
        {v | ∃ k : Fin n.succ, prefSum v k < a} :=
      (Measure.map_apply hRevMeas hEvent).symm
    _ = μ {v | ∃ k : Fin n.succ, prefSum v k < a} := by
      rw [hrev]

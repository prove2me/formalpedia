-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_finite_actual_jump_cell_test_sum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:15:26.687884+00:00
-- url     : https://prove2.me/submissions/cafd59a5-2501-46ab-b92c-008e8fea18a6

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

/-- Every finite set of genuine jump times admits actual uniform half-open
cells whose complete continuous test sum converges to the finite jump sum. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (S : Finset ℝ≥0)
    (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hL : ∀ u ∈ S,
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u) :
    ∃ idx : ℝ≥0 → ℕ → ℕ,
      (∀ u ∈ S, ∀ n, idx u n ≤ n ∧
        (idx u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
        u ≤ ((idx u n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∧
      Tendsto (fun n : ℕ =>
        ∑ u ∈ S, f (Y (((idx u n + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1))) -
          Y ((idx u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by
  classical
  let d : ℕ → ℝ≥0 := fun n => T / ((n : ℝ≥0) + 1)
  have hcell (u : ℝ≥0) (hu : u ∈ S) : ∃ i : ℕ → ℕ,
      (∀ n, i n ≤ n ∧ (i n : ℝ≥0) * d n < u ∧
        u ≤ ((i n + 1 : ℕ) : ℝ≥0) * d n) ∧
      Tendsto (fun n => (i n : ℝ≥0) * d n) atTop (𝓝[<] u) ∧
      Tendsto (fun n => ((i n + 1 : ℕ) : ℝ≥0) * d n)
        atTop (nhdsWithin u (Ici u)) := by
    simpa only [d] using avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
      T u hT (hTimes u hu).1 (hTimes u hu).2
  let idx : ℝ≥0 → ℕ → ℕ := fun u =>
    if hu : u ∈ S then Classical.choose (hcell u hu) else fun _ => 0
  have hspec (u : ℝ≥0) (hu : u ∈ S) :
      (∀ n, idx u n ≤ n ∧ (idx u n : ℝ≥0) * d n < u ∧
        u ≤ ((idx u n + 1 : ℕ) : ℝ≥0) * d n) ∧
      Tendsto (fun n => (idx u n : ℝ≥0) * d n) atTop (𝓝[<] u) ∧
      Tendsto (fun n => ((idx u n + 1 : ℕ) : ℝ≥0) * d n)
        atTop (nhdsWithin u (Ici u)) := by
    simpa only [idx, dif_pos hu] using Classical.choose_spec (hcell u hu)
  let a : ℝ≥0 → ℕ → ℝ≥0 := fun u n => (idx u n : ℝ≥0) * d n
  let b : ℝ≥0 → ℕ → ℝ≥0 :=
    fun u n => ((idx u n + 1 : ℕ) : ℝ≥0) * d n
  have hpoint (u : ℝ≥0) (hu : u ∈ S) :
      Tendsto (fun n => f (Y (b u n) - Y (a u n))) atTop
        (𝓝 (f (Y u - Function.leftLim Y u))) := by
    have hinc : Tendsto (fun n => Y (b u n) - Y (a u n)) atTop
        (𝓝 (Y u - Function.leftLim Y u)) :=
      avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump
        Y u (a u) (b u) (hspec u hu).2.1 (hspec u hu).2.2
        (hL u hu) (hR u hu)
    exact (hf.tendsto _).comp hinc
  have hsum :
      Tendsto (fun n => ∑ u ∈ S, f (Y (b u n) - Y (a u n))) atTop
        (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) :=
    tendsto_finset_sum S hpoint
  refine ⟨idx, ?_, ?_⟩
  · intro u hu n
    exact (hspec u hu).1 n
  · simpa only [a, b, d] using hsum

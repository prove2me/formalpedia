-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_uniform_mesh_cell_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:04:00.07825+00:00
-- url     : https://prove2.me/submissions/44ec1143-7ea6-4734-b9e2-589a83858801

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (B : ℝ≥0) (hB : 0 < B) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    (∀ n, StrictMono (u n)) ∧ (∀ n, 0 < h n) ∧
      (∀ n i, i ∈ Finset.range (n + 1) →
        u n i ≤ B ∧ u n (i + 1) ≤ B ∧ (u n (i + 1) : ℝ) - (u n i : ℝ) = h n) := by
  intro u h
  have hu (n : ℕ) : StrictMono (u n) := by
    intro i j hij
    dsimp only [u]
    apply (div_lt_div_iff_of_pos_right (by positivity :
      (0 : ℝ≥0) < ((n + 1 : ℕ) : ℝ≥0))).2
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) hB
  have hend (n : ℕ) : u n (n + 1) = B := by
    have hn : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := ne_of_gt (by positivity)
    simp [u, hn]
  have hnode (n i : ℕ) (hi : i ≤ n + 1) : u n i ≤ B := by
    simpa only [hend] using (hu n).monotone hi
  refine ⟨hu, ?_, ?_⟩
  · intro n
    exact div_pos (by exact_mod_cast hB) (by positivity)
  · intro n i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    refine ⟨hnode n i (by omega), hnode n (i + 1) (by omega), ?_⟩
    dsimp only [u, h]
    push_cast
    ring

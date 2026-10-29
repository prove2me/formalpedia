-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_fold_horizon_vs_top_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:19:16.148766+00:00
-- url     : https://prove2.me/submissions/a3ebe077-1c12-4daa-95b3-eec0d5558316

import Mathlib
open Set
open scoped ENNReal Classical
theorem solution
    (L : List ℕ) (x : ℕ → ℝ≥0∞) (hit : ℕ → Prop)
    (H T : ℝ≥0∞) (hTH : T ≤ H) :
    L.foldr (fun k u => (if hit k then x k else H) ⊓ u) T =
      L.foldr (fun k u => (if hit k then x k else ⊤) ⊓ u) T := by
  have key : L.foldr (fun k u => (if hit k then x k else H) ⊓ u) T =
      L.foldr (fun k u => (if hit k then x k else ⊤) ⊓ u) T ∧
      L.foldr (fun k u => (if hit k then x k else ⊤) ⊓ u) T ≤ T := by
    induction L with
    | nil => simp
    | cons a L ih =>
      simp only [List.foldr_cons]
      rw [ih.1]
      refine ⟨?_, inf_le_right.trans ih.2⟩
      split_ifs
      · rfl
      · rw [top_inf_eq, inf_eq_right.2 (ih.2.trans hTH)]
  exact key.1

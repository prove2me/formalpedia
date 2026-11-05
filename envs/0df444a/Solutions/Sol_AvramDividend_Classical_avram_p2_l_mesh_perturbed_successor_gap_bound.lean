-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_perturbed_successor_gap_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:41:17.11925+00:00
-- url     : https://prove2.me/submissions/682f163a-8c57-4378-bf2b-557c484a6433

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-- The radius of simultaneous endpoint perturbations controls each mesh gap. -/
theorem solution {n : ℕ} (x y : Fin (n + 1) → ℝ) (r h : ℝ)
    (hwindow : ∀ i : Fin (n + 1), |y i - x i| < r)
    (hnom : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) :
    ∀ i : Fin n, y i.succ - y i.castSucc < h + 2 * r := by
  intro i
  have hlo := hwindow i.castSucc
  have hhi := hwindow i.succ
  rw [abs_lt] at hlo hhi
  have hgap := hnom i
  rcases hlo with ⟨hloLeft, hloRight⟩
  rcases hhi with ⟨hhiLeft, hhiRight⟩
  linarith

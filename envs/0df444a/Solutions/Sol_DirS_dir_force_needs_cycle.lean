-- Prove2me | solution 1 for DirS.dir_force_needs_cycle
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:40:31.018838+00:00
-- url     : https://prove2.me/submissions/ea45fb7e-efa5-4a1f-8dc8-38764ebaa6a6

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw
open DirS

/-- The directed path 0 -> 1 -> 2. -/
def g73t_path : OriGraph 3 where
  edge x y := decide (x.val + 1 = y.val)
  no_loop := by decide
  no_two_cycle := by decide

theorem g73t_path_not_homToEdge : ¬ homToEdge g73t_path := by
  rintro ⟨c, hc⟩
  have h1 := (hc 0 1 (by decide)).2
  have h2 := (hc 1 2 (by decide)).1
  rw [h1] at h2
  exact Bool.noConfusion h2

theorem g73t_dirForcing_true {m : ℕ} (B : OriGraph m) : DirForcing B := by
  intro q _ _ ε _
  exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩

theorem solution : ¬ (∀ {m : ℕ} (B : OriGraph m) (h : DirForcing B), homToEdge B ∧ hasCycle B) := by
  intro H
  exact g73t_path_not_homToEdge (H g73t_path (g73t_dirForcing_true _)).1

-- Prove2me | solution 1 for DirS.dir_force_needs_edge
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:40:30.068109+00:00
-- url     : https://prove2.me/submissions/6466c949-0765-4e69-9060-048a6d2070ff

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

theorem solution : ¬ (∀ {m : ℕ} (B : OriGraph m) (h : DirForcing B), homToEdge B) := by
  intro H
  exact g73t_path_not_homToEdge (H g73t_path (g73t_dirForcing_true _))

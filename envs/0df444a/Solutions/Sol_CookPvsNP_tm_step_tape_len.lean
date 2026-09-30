-- Prove2me | solution 1 for CookPvsNP.tm_step_tape_len
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T07:35:51.239169+00:00
-- url     : https://prove2.me/submissions/7a6aa9aa-4ee2-4906-b672-0433ab445f2d

import Mathlib
import Definitions.Def_CookPvsNP_defs

open CookPvsNP

variable {Γ : Type} {Q : Type} (M : TM Γ)

theorem solution (c : Cfg Γ M.Q) :
    (M.step c).left.length + (M.step c).right.length ≤ c.left.length + c.right.length + 1 := by
  unfold TM.step
  split
  · exact Nat.le_add_right _ _
  · obtain ⟨q', s', h⟩ := M.δ c.state c.head
    cases h with
    | right =>
        simp only [Cfg.left, Cfg.right, Cfg.head, List.length_cons, List.length_tail]
        cases c.right with
        | nil => simp
        | cons b r => omega
    | left =>
        cases c.left with
        | nil => simp only [Cfg.left, Cfg.right, Cfg.head, List.length_cons]; omega
        | cons a x' =>
            simp only [Cfg.left, Cfg.right, Cfg.head, List.length_cons, List.length_tail]
            omega

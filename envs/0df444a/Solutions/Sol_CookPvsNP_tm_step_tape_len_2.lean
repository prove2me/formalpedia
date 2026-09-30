-- Prove2me | solution 2 for CookPvsNP.tm_step_tape_len
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T07:35:59.222033+00:00
-- url     : https://prove2.me/submissions/317f74ea-9f2c-4125-bf4c-fd0ea28f4bd2

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
            simp only [Cfg.left, Cfg.right, Cfg.head, List.length_cons, List.length_tail]; omega

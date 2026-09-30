-- Prove2me | solution 1 for CookPvsNP.tm_run_tape_len
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T09:01:13.639985+00:00
-- url     : https://prove2.me/submissions/d304943d-03bf-4585-b79f-17a238afe2ac

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_CookPvsNP_tm_step_tape_len

open CookPvsNP

variable {Γ : Type} {Q : Type} (M : TM Γ)

theorem solution (n : ℕ) (c : Cfg Γ M.Q) :
    (M.run n c).left.length + (M.run n c).right.length ≤ n + c.left.length + c.right.length := by
  induction n generalizing c with
  | zero => simp [TM.run]
  | succ n ih =>
      have hrun : M.run (Nat.succ n) c = M.step (M.run n c) := by
        show M.step^[Nat.succ n] c = M.step (M.step^[n] c)
        exact Function.iterate_succ_apply' M.step n c
      rw [hrun]
      have hstep := tm_step_tape_len (M := M) (M.run n c)
      have ih' := ih c
      omega

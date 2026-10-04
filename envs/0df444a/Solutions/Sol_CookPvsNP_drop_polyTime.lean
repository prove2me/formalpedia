-- Prove2me | solution 1 for CookPvsNP.drop_polyTime
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T17:15:04.896979+00:00
-- url     : https://prove2.me/submissions/81323e89-b6ea-4bfc-a9d5-17adaf811f71

import Theorems.Thm_CookPvsNP_stack_program_polytime

set_option autoImplicit false
open CookPvsNP

private def dropProgram (A : Type) : ℕ → StackProg Unit A
  | 0 => .act (fun _ _ => .keep)
  | n + 1 => .seq (.act (fun _ _ => .pop)) (dropProgram A n)

private theorem drop_exec {A : Type} (n : ℕ) (s : Unit → List A) :
    (dropProgram A n).Exec s (fun i => (s i).drop n) (2 * n + 1) := by
  induction n generalizing s with
  | zero =>
    change StackProg.Exec (.act (fun _ _ => .keep)) s s 1
    exact StackProg.Exec.act (fun _ _ => StackAct.keep) s
  | succ n ih =>
    have h := (StackProg.Exec.act (fun _ _ => StackAct.pop) s).seq
      (ih (StackProg.applyAct (fun _ _ => StackAct.pop) s))
    simpa [dropProgram, StackProg.applyAct, StackAct.apply, List.drop_tail,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Removing any fixed number of initial letters is polynomial-time computable
in the original Cook single-tape model, including on words shorter than that number. -/
theorem solution {A : Type} [Fintype A] [DecidableEq A] (n : ℕ) :
    PolyTimeComputable (fun w : List A => w.drop n) := by
  apply stack_program_polytime (dropProgram A n) () () _ (2 * n + 1)
  intro w
  refine ⟨fun _ => w.drop n, 2 * n + 1, by omega, ?_, rfl⟩
  simpa using drop_exec n (fun _ : Unit => w)

#print axioms solution

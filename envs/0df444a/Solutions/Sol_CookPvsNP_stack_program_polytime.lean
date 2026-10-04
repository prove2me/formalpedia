-- Prove2me | solution 1 for CookPvsNP.stack_program_polytime
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:45.820562+00:00
-- url     : https://prove2.me/submissions/248fb00b-b3aa-46b2-853d-2b599416db5a

import Definitions.Def_CookPvsNP_StackProgram
import Theorems.Thm_CookPvsNP_stack_program_correct
import Theorems.Thm_CookPvsNP_stack_polytime

set_option autoImplicit false
open CookPvsNP

theorem solution {K A : Type} [Fintype K] [Fintype A] [DecidableEq K] [DecidableEq A]
    (p : StackProg K A) (ki ko : K) (f : List A → List A) (k : ℕ)
    (h : ∀ w : List A, ∃ s n, n ≤ w.length ^ k + k ∧
      p.Exec (fun j => if j = ki then w else []) s n ∧ s ko = f w) :
    PolyTimeComputable f := by
  apply stack_polytime p.machine ki ko f k
  intro w
  obtain ⟨s, n, hn, he, ho⟩ := h w
  obtain ⟨l, hd, hr⟩ := stack_program_correct he
  refine ⟨n, hn, ?_, ?_⟩
  · change p.done ((p.machine.step^[n]) ⟨p.entry, fun j => if j = ki then w else []⟩).state = true
    rw [hr]
    exact hd
  · change ((p.machine.step^[n]) ⟨p.entry, fun j => if j = ki then w else []⟩).store ko = f w
    rw [hr]
    exact ho

#print axioms solution

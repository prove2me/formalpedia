-- Prove2me | solution 1 for CookPvsNP.stack_sweep_left
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T11:47:05.06827+00:00
-- url     : https://prove2.me/submissions/c012535d-a2a5-4f90-8be7-36cb5b86f0e2

import Definitions.Def_CookPvsNP_StackCompiler

set_option autoImplicit false
open CookPvsNP

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q) (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) (R : List (Option (StackSym K A))) :
    (stackTM P ki ko).run r.length
      ⟨.scanL q a c,
        (r.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (r.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none, R⟩ =
      ⟨.scanL q a (stackLeft a c r).1, [], some (StackSym.origin (K := K) (A := A)),
        ((stackLeft a c r).2.map (some ∘ StackSym.work)).reverse ++ R⟩ := by
  induction r generalizing c R with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    have hs : (stackTM P ki ko).step
        ⟨.scanL q a c, xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))], some (.work x), R⟩ =
        ⟨.scanL q a x, (xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
          (xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
          some (.work (stackPopCell a c x)) :: R⟩ := by
      cases xs <;> simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((stackTM P ki ko).step^[xs.length]) hs).trans ?_
    simpa [TM.run, stackLeft, List.reverse_cons, List.append_assoc] using
      ih x (some (.work (stackPopCell a c x)) :: R)

#print axioms solution

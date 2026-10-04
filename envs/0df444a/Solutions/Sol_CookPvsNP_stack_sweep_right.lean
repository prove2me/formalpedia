-- Prove2me | solution 1 for CookPvsNP.stack_sweep_right
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T11:47:04.332509+00:00
-- url     : https://prove2.me/submissions/4e9ffba1-4372-48bd-b1e7-111c9c991dde

import Definitions.Def_CookPvsNP_StackCompiler

set_option autoImplicit false
open CookPvsNP

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q) (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) (L : List (Option (StackSym K A))) :
    (stackTM P ki ko).run r.length
      ⟨.scanR q a c, L, (r.map (some ∘ StackSym.work)).headD none,
        (r.map (some ∘ StackSym.work)).tail⟩ =
      ⟨.scanR q a (stackRight a c r).1,
        ((stackRight a c r).2.map (some ∘ StackSym.work)).reverse ++ L, none, []⟩ := by
  induction r generalizing c L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.headD_cons, List.tail_cons]
    have hs : (stackTM P ki ko).step
        ⟨.scanR q a c, L, some (.work x), xs.map (some ∘ StackSym.work)⟩ =
        ⟨.scanR q a (stackPushNext a x), some (.work (stackPushCell a c x)) :: L,
          (xs.map (some ∘ StackSym.work)).headD none,
          (xs.map (some ∘ StackSym.work)).tail⟩ := by
      simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((stackTM P ki ko).step^[xs.length]) hs).trans ?_
    simpa [TM.run, stackRight, List.reverse_cons, List.append_assoc] using
      ih (stackPushNext a x) (some (.work (stackPushCell a c x)) :: L)

#print axioms solution

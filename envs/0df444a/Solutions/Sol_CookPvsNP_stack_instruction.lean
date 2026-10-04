-- Prove2me | solution 1 for CookPvsNP.stack_instruction
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:34.791278+00:00
-- url     : https://prove2.me/submissions/80d2b988-ba16-48b2-befc-7521e5bf05c0

import Definitions.Def_CookPvsNP_StackRepresentation
import Theorems.Thm_CookPvsNP_stack_sweep_right
import Theorems.Thm_CookPvsNP_stack_sweep_left
import Theorems.Thm_CookPvsNP_stack_sweep_algebra

set_option autoImplicit false
open CookPvsNP

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q)
    (x : StackCol K A) (xs : List (StackCol K A)) (hq : P.done q = false) :
    let d := P.next q x
    (stackTM P ki ko).run (2 * (x :: xs).length + 2) (stackFrame q (x :: xs)) =
      stackFrame d.1 (stackBackward d.2 (stackForward d.2 (stackPushCarry d.2) (x :: xs))) := by
  let d := P.next q x
  let a := d.2
  let c := stackPushCarry a
  let z := stackRight a c (x :: xs)
  let out := stackBackward a (stackForward a c (x :: xs))
  let M := stackTM P ki ko
  have hfirst : (M).run 1 (stackFrame q (x :: xs)) =
      ⟨.scanR d.1 a (stackPushNext a x), some (.work (stackPushCell a c x)) :: [some (StackSym.origin (K := K) (A := A))],
        (xs.map (some ∘ StackSym.work)).headD none,
        (xs.map (some ∘ StackSym.work)).tail⟩ := by
    simp [M, TM.run, TM.step, TM.IsHalting, stackTM, stackFrame, hq, d, a, c]
  have hright := stack_sweep_right P ki ko d.1 a (stackPushNext a x) xs
    [some (.work (stackPushCell a c x)), some (StackSym.origin (K := K) (A := A))]
  have hb : (M).run 1
      ⟨.scanR d.1 a z.1, (z.2.map (some ∘ StackSym.work)).reverse ++ [some (StackSym.origin (K := K) (A := A))], none, []⟩ =
      ⟨.scanL d.1 a z.1, ((z.2.reverse.map (some ∘ StackSym.work)) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        ((z.2.reverse.map (some ∘ StackSym.work)) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
        [some (.work z.1)]⟩ := by
    cases h : z.2.reverse <;>
      simp [M, TM.run, TM.step, TM.IsHalting, stackTM, ← List.map_reverse, h]
  have hleft := stack_sweep_left P ki ko d.1 a z.1 z.2.reverse [some (.work z.1)]
  have hlen : z.2.length = (x :: xs).length := (stack_sweep_algebra a (x :: xs)).1
  have hout : (stackLeft a z.1 z.2.reverse).2.reverse ++ [z.1] = out :=
    (stack_sweep_algebra a (x :: xs)).2
  have hf : (M).run 1
      ⟨.scanL d.1 a (stackLeft a z.1 z.2.reverse).1, [], some (StackSym.origin (K := K) (A := A)),
        ((stackLeft a z.1 z.2.reverse).2.map (some ∘ StackSym.work)).reverse ++
          [some (.work z.1)]⟩ = stackFrame d.1 out := by
    have hm := congrArg (List.map (some ∘ StackSym.work)) hout
    simp only [List.map_append, List.map_reverse, List.map_cons, List.map_nil,
      Function.comp_apply] at hm
    simp only [M, TM.run, Function.iterate_one, TM.step, TM.IsHalting, stackTM]
    simp only [StackQ.scanL.injEq, reduceCtorEq, or_self, ↓reduceIte]
    simpa [stackFrame] using congrArg
      (fun r : List (Option (StackSym K A)) =>
        (⟨StackQ.ready d.1, [some (StackSym.origin (K := K) (A := A))], r.headD none, r.tail⟩ :
          Cfg (StackSym K A) (StackQ K A Q))) hm
  change (M).run _ _ = stackFrame d.1 out
  have hr : (M).run xs.length ((M).run 1 (stackFrame q (x :: xs))) =
      ⟨.scanR d.1 a z.1, (z.2.map (some ∘ StackSym.work)).reverse ++ [some (StackSym.origin (K := K) (A := A))], none, []⟩ := by
    rw [hfirst]
    simpa [M, z, stackRight, List.reverse_cons, List.append_assoc] using hright
  rw [List.length_reverse, hlen] at hleft
  rw [show 2 * (x :: xs).length + 2 = 1 + ((x :: xs).length + (1 + (xs.length + 1))) by simp; omega]
  unfold TM.run at hr hb hleft hf ⊢
  dsimp only [M, stackTM] at hr hb hleft hf ⊢
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_add_apply, hr, hb, hleft]
  exact hf

#print axioms solution

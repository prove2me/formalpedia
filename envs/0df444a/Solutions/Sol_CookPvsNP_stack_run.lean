-- Prove2me | solution 1 for CookPvsNP.stack_run
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:38.025647+00:00
-- url     : https://prove2.me/submissions/27fda865-88ac-40c6-8e5e-4c849fbe433d

import Definitions.Def_CookPvsNP_StackRepresentation
import Theorems.Thm_CookPvsNP_stack_instruction
import Theorems.Thm_CookPvsNP_stack_representation
import Theorems.Thm_CookPvsNP_stack_column_laws

set_option autoImplicit false
open CookPvsNP

private theorem rep_head {K A : Type} (x : StackCol K A) (xs : List (StackCol K A))
    (s : K → List A) (h : StackRep (x :: xs) s) : x = fun k => (s k).head? := by
  funext k
  have hh := congrArg (fun l : List (Option A) => l.headD none) (h k).2
  simp only [List.map_cons, List.headD_cons] at hh
  rw [hh]
  cases he : s k with
  | nil => simp [stackPad, he, List.replicate_succ]
  | cons b bs => simp [stackPad, he]

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (m : ℕ)
    (c : StackCfg K A Q) (r : List (StackCol K A)) (hn : 0 < r.length)
    (hr : StackRep r c.store) :
    ∃ t r', t ≤ stackTime r.length m ∧ r'.length ≤ r.length + m ∧ 0 < r'.length ∧
      StackRep r' ((P.step^[m]) c).store ∧
      (stackTM P ki ko).run t (stackFrame c.state r) =
        stackFrame ((P.step^[m]) c).state r' := by
  induction m generalizing c r with
  | zero => exact ⟨0, r, by simp [stackTime], by simp, hn, hr, rfl⟩
  | succ m ih =>
    by_cases hd : P.done c.state = true
    · have hf : P.step c = c := by simp [StackMachine.step, hd]
      have he : (P.step^[m + 1]) c = c := Function.iterate_fixed hf _
      exact ⟨0, r, Nat.zero_le _, by omega, hn, he.symm ▸ hr, by rw [he]; rfl⟩
    · have hd' : P.done c.state = false := Bool.eq_false_iff.mpr hd
      cases r with
      | nil => simp at hn
      | cons x xs =>
        let a := (P.next c.state x).2
        let z := stackBackward a (stackForward a (stackPushCarry a) (x :: xs))
        have hx := rep_head x xs c.store hr
        have hc : P.step c = ⟨(P.next c.state x).1, fun k => (a k).apply (c.store k)⟩ := by
          simp only [StackMachine.step, hd', Bool.false_eq_true, ↓reduceIte]
          rw [← hx]
        have hl : z.length = (x :: xs).length + 1 := (stack_column_laws a (x :: xs) ki).1
        have hz : StackRep z (P.step c).store := by
          rw [hc]
          exact stack_representation a (x :: xs) c.store hr
        have ht : (stackTM P ki ko).run (2 * (x :: xs).length + 2)
            (stackFrame c.state (x :: xs)) = stackFrame (P.step c).state z := by
          rw [hc]
          exact stack_instruction P ki ko c.state x xs hd'
        obtain ⟨t, r', htbound, hwidth, hpos, hrep, hrun⟩ := ih (P.step c) z (by omega) hz
        refine ⟨t + (2 * (x :: xs).length + 2), r', ?_, ?_, hpos, ?_, ?_⟩
        · rw [hl] at htbound
          unfold stackTime at htbound ⊢
          nlinarith
        · omega
        · simpa only [Function.iterate_succ_apply] using hrep
        · have hh := (congrArg ((stackTM P ki ko).run t) ht).trans hrun
          unfold TM.run at hh ⊢
          dsimp only [stackTM] at hh ⊢
          rw [Function.iterate_add_apply]
          simpa only [Function.iterate_succ_apply] using hh

#print axioms solution

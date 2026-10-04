-- Prove2me | solution 1 for CookPvsNP.stack_sweep_algebra
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T11:22:32.738287+00:00
-- url     : https://prove2.me/submissions/89fd4899-1164-4a48-b6cb-fc97d45b2e07

import Definitions.Def_CookPvsNP_StackModel

set_option autoImplicit false
open CookPvsNP

private theorem right_form {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) :
    (stackRight a c r).2 ++ [(stackRight a c r).1] = stackForward a c r := by
  induction r generalizing c with
  | nil => rfl
  | cons x xs ih =>
    simpa [stackRight, stackForward] using
      congrArg (fun z => stackPushCell a c x :: z) (ih (stackPushNext a x))

private theorem right_length {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) :
    (stackRight a c r).2.length = r.length := by
  induction r generalizing c with
  | nil => rfl
  | cons x xs ih => simp [stackRight, ih]

private theorem right_neutral {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) (c : StackCol K A)
    (hc : ∀ k, a k = .pop → c k = none) :
    stackPopCell a stackZero (stackRight a c r).1 = (stackRight a c r).1 := by
  have hn : ∀ k, a k = .pop → (stackRight a c r).1 k = none := by
    induction r generalizing c with
    | nil => exact hc
    | cons x xs ih =>
      apply ih
      intro k hk
      simp [stackPushNext, hk]
  funext k
  cases h : a k with
  | keep => simp [stackPopCell, h]
  | push b => simp [stackPopCell, h]
  | pop => simp [stackPopCell, stackZero, h, hn k h]

private theorem left_append {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r s : List (StackCol K A)) :
    stackLeft a c (r ++ s) =
      let x := stackLeft a c r
      let y := stackLeft a x.1 s
      (y.1, x.2 ++ y.2) := by
  induction r generalizing c with
  | nil => rfl
  | cons x xs ih => simp [stackLeft, ih]

private theorem left_state {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) :
    (stackLeft a c r.reverse).1 = r.headD c := by
  cases r with
  | nil => rfl
  | cons x xs => simp [List.reverse_cons, left_append, stackLeft]

private theorem left_form {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) (c : StackCol K A)
    (hc : stackPopCell a stackZero c = c) :
    (stackLeft a c r.reverse).2.reverse ++ [c] = stackBackward a (r ++ [c]) := by
  induction r with
  | nil => simp [stackLeft, stackBackward, hc]
  | cons x xs ih =>
    simp only [List.reverse_cons, left_append, stackLeft, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc, ih, left_state, stackBackward]
    cases xs <;> rfl

theorem solution {K A : Type} (a : K → StackAct A) (r : List (StackCol K A)) :
    let z := stackRight a (stackPushCarry a) r
    z.2.length = r.length ∧
    (stackLeft a z.1 z.2.reverse).2.reverse ++ [z.1] =
      stackBackward a (stackForward a (stackPushCarry a) r) := by
  dsimp only
  refine ⟨right_length _ _ _, ?_⟩
  rw [left_form, right_form]
  apply right_neutral
  intro k hk
  simp [stackPushCarry, hk]

#print axioms solution

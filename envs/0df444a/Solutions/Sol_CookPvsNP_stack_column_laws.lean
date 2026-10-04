-- Prove2me | solution 1 for CookPvsNP.stack_column_laws
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T11:22:30.882049+00:00
-- url     : https://prove2.me/submissions/154eaf76-a519-42a6-a3d9-807ccfe07a8c

import Definitions.Def_CookPvsNP_StackModel

set_option autoImplicit false
open CookPvsNP

private theorem forward_length {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) :
    (stackForward a c r).length = r.length + 1 := by
  induction r generalizing c with
  | nil => rfl
  | cons x xs ih => simp [stackForward, ih]

private theorem forward_projection {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) (k : K)
    (hc : a k = .keep ∨ a k = .pop → c k = none) :
    (stackForward a c r).map (fun (v : StackCol K A) => v k) =
      match a k with
      | .push _ => c k :: r.map (fun (v : StackCol K A) => v k)
      | _ => r.map (fun (v : StackCol K A) => v k) ++ [none] := by
  induction r generalizing c with
  | nil => cases h : a k <;> simp [stackForward, hc, h]
  | cons x xs ih =>
    have hn : a k = .keep ∨ a k = .pop → stackPushNext a x k = none := by
      rintro (h | h) <;> simp [stackPushNext, h]
    simp only [stackForward, List.map_cons, ih _ hn]
    cases h : a k <;> simp [stackPushCell, stackPushNext, h]

private theorem backward_length {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) : (stackBackward a r).length = r.length := by
  induction r with
  | nil => rfl
  | cons x xs ih => simp [stackBackward, ih]

private theorem backward_projection {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) (k : K) :
    (stackBackward a r).map (fun (v : StackCol K A) => v k) =
      match a k with
      | .pop => (r.map (fun (v : StackCol K A) => v k)).tail ++ List.replicate (min 1 r.length) none
      | _ => r.map (fun (v : StackCol K A) => v k) := by
  induction r with
  | nil => cases a k <;> rfl
  | cons x xs ih =>
    simp only [stackBackward, List.map_cons, ih]
    cases h : a k with
    | keep => simp [stackPopCell, h]
    | push b => simp [stackPopCell, h]
    | pop => cases xs with
      | nil => simp [stackPopCell, h, stackZero]
      | cons y ys => simp [stackPopCell, h]

theorem solution {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) (k : K) :
    let r' := stackBackward a (stackForward a (stackPushCarry a) r)
    r'.length = r.length + 1 ∧
    r'.map (fun (v : StackCol K A) => v k) =
      match a k with
      | .keep => r.map (fun (v : StackCol K A) => v k) ++ [none]
      | .push b => some b :: r.map (fun (x : StackCol K A) => x k)
      | .pop => (r.map (fun (v : StackCol K A) => v k) ++ [none]).tail ++ [none] := by
  dsimp only
  constructor
  · rw [backward_length, forward_length]
  · have hc : a k = .keep ∨ a k = .pop → stackPushCarry a k = none := by
      rintro (h | h) <;> simp [stackPushCarry, h]
    rw [backward_projection, forward_projection _ _ _ _ hc, forward_length]
    cases h : a k <;> simp [h, stackPushCarry]

#print axioms solution

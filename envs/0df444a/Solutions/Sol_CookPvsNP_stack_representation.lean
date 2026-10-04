-- Prove2me | solution 1 for CookPvsNP.stack_representation
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:33.868769+00:00
-- url     : https://prove2.me/submissions/d9a62091-4730-4323-b733-d134be352aa0

import Definitions.Def_CookPvsNP_StackRepresentation
import Theorems.Thm_CookPvsNP_stack_column_laws

set_option autoImplicit false
open CookPvsNP

private theorem pad_action {A : Type} (a : StackAct A) (s : List A)
    (n : ℕ) (hn : s.length ≤ n) :
    (a.apply s).length ≤ n + 1 ∧
    stackPad (a.apply s) (n + 1) =
      match a with
      | .keep => stackPad s n ++ [none]
      | .push b => some b :: stackPad s n
      | .pop => (stackPad s n ++ [none]).tail ++ [none] := by
  cases a with
  | keep =>
    constructor
    · simpa [StackAct.apply] using hn.trans (Nat.le_succ n)
    · simp only [StackAct.apply, stackPad]
      rw [show n + 1 - s.length = (n - s.length) + 1 by omega]
      simp [List.replicate_add, List.append_assoc]
  | push b => simp [StackAct.apply, stackPad, hn, Nat.succ_le_succ]
  | pop =>
    cases s with
    | nil =>
      simp only [StackAct.apply, List.tail_nil, List.length_nil, Nat.zero_le, true_and,
        stackPad, List.map_nil, Nat.sub_zero, List.nil_append]
      have he : List.replicate n (none : Option A) ++ [none] = List.replicate (n + 1) none := by
        simpa using (List.replicate_add n 1 (none : Option A)).symm
      rw [he, List.replicate_succ, List.tail_cons]
      simpa [List.replicate_succ] using he.symm
    | cons b bs =>
      simp only [List.length_cons] at hn
      constructor
      · simp only [StackAct.apply, List.tail_cons]; omega
      · simp only [StackAct.apply, List.tail_cons, stackPad, List.map_cons, List.length_cons,
          List.cons_append, List.tail_cons]
        rw [show n + 1 - bs.length = (n - (bs.length + 1)) + 2 by omega]
        simp [List.replicate_add, List.append_assoc]

theorem solution {K A : Type} (a : K → StackAct A) (r : List (StackCol K A))
    (s : K → List A) (h : StackRep r s) :
    StackRep (stackBackward a (stackForward a (stackPushCarry a) r))
      (fun k => (a k).apply (s k)) := by
  intro k
  obtain ⟨hlen, hproj⟩ := stack_column_laws a r k
  obtain ⟨hsize, hpad⟩ := pad_action (a k) (s k) r.length (h k).1
  refine ⟨hlen.symm ▸ hsize, ?_⟩
  rw [hlen, hpad, hproj, (h k).2]
  rfl

#print axioms solution

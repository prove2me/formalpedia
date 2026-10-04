-- Prove2me | solution 1 for CookPvsNP.stack_output
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:36.9829+00:00
-- url     : https://prove2.me/submissions/1fd65d28-5919-464a-b1cf-b1e96951dd69

import Definitions.Def_CookPvsNP_StackRepresentation

set_option autoImplicit false
open CookPvsNP

private theorem trim_blanks {Γ : Type} (xs : List (Option Γ)) (n : ℕ) :
    ((xs ++ List.replicate n none).reverse.dropWhile Option.isNone).reverse =
      (xs.reverse.dropWhile Option.isNone).reverse := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    simpa using ih

private theorem trim_word {Γ : Type} (xs : List Γ) :
    ((xs.map some).reverse.dropWhile Option.isNone).reverse = xs.map some := by
  have h (ys : List Γ) : (ys.map some).dropWhile Option.isNone = ys.map some := by
    cases ys <;> simp
  rw [← List.map_reverse, h, ← List.map_reverse, List.reverse_reverse]

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (r : List (StackCol K A))
    (s : K → List A) (hr : StackRep r s) :
    let out := r.map (fun v => (v ko).map (StackSym.output (K := K))) ++ [none]
    (stackTM P ki ko).output
      ⟨.accept, [some .origin], out.headD none, out.tail⟩ =
      (s ko).map (some ∘ stackOutput) := by
  dsimp only
  have hm := congrArg (List.map (Option.map (StackSym.output (K := K)))) (hr ko).2
  simp only [List.map_map, Function.comp_def, stackPad, List.map_append,
    List.map_replicate, Option.map_none, Option.map_some] at hm
  rw [hm]
  have hne : (List.map (fun a => some (StackSym.output (K := K) a)) (s ko) ++
      List.replicate (r.length - (s ko).length) none ++ [none]) ≠ [] := by simp
  simp only [TM.output]
  have hcons : (List.map (fun a => some (StackSym.output (K := K) a)) (s ko) ++
      List.replicate (r.length - (s ko).length) none ++ [none]).headD none ::
      (List.map (fun a => some (StackSym.output (K := K) a)) (s ko) ++
      List.replicate (r.length - (s ko).length) none ++ [none]).tail =
      List.map (fun a => some (StackSym.output (K := K) a)) (s ko) ++
      List.replicate (r.length - (s ko).length) none ++ [none] := by
    generalize he : (List.map (fun a => some (StackSym.output (K := K) a)) (s ko) ++
      List.replicate (r.length - (s ko).length) none ++ [none]) = l at *
    cases l with
    | nil => contradiction
    | cons _ _ => rfl
  rw [hcons]
  rw [List.append_assoc, show List.replicate (r.length - (s ko).length) (none : Option (StackSym K A)) ++ [none] =
      List.replicate (r.length - (s ko).length + 1) none by rw [List.replicate_succ']]
  rw [trim_blanks]
  have hw := trim_word ((s ko).map (StackSym.output (K := K)))
  simp only [List.map_map] at hw
  convert hw using 1 <;> rfl

#print axioms solution

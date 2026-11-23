-- Prove2me | solution 1 for DecisionTree.relabel_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:54.019458+00:00
-- url     : https://prove2.me/submissions/e2304668-f943-4ae8-9f1c-391fcdda8227

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_DecisionTree

set_option autoImplicit true
open DecisionTree
namespace DecisionTree
theorem _root_.solution {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n} {h : ∀ i i' : Fin n, T1.usesVar i → T2.usesVar i' → f i = f i' → i = i'} :
    relabel hf T1 = relabel hf T2 → T1 = T2 := by
  intro h
  cases T1 with
  | leaf _ =>
    cases T2 with
    | leaf _ => simp only [relabel] at h; simp_all
    | branch _ _ _ => contradiction
  | branch i tl th =>
    cases T2 with
    | leaf _ => contradiction
    | branch i' tl' th' =>
      simp only [relabel] at h
      injection h with a b c
      rw [solution b (hf := hf) (f := f)]
      rw [solution c (hf := hf) (f := f)]
      simp_all only [Fin.mk.injEq, branch.injEq, and_self, and_true]
      apply h
      · exact .here
      · exact .here
      · exact a
      · intro ii ii' hii hii' hfi
        apply h _ _ (usesVar.high hii) (usesVar.high hii') hfi
      · intro ii ii' hii hii' hfi
        apply h _ _ (usesVar.low hii) (usesVar.low hii') hfi
end DecisionTree

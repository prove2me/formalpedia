-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.runWord_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:51.856144+00:00
-- url     : https://prove2.me/submissions/9f34dfea-0d38-4e25-b3ac-71f463b39e33

module
public import Definitions.Def_BalanceSpecificaton_OneSidedExample
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Theorems.Thm_BalanceSpecification_OneSidedExample_edgeLabel_injective

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (s : Vertex) : Function.Injective (runWord s) := by
  intro xs
  induction xs generalizing s with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys => cases h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => cases h
    | cons y ys =>
      have heq := List.cons.inj h
      have hxy := edgeLabel_injective s heq.1
      subst y
      exact congrArg (List.cons x) (ih (edgeTarget s x) heq.2)
end BalanceSpecification.OneSidedExample

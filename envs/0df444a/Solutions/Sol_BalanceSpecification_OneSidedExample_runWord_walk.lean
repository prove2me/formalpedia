-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.runWord_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:27.701179+00:00
-- url     : https://prove2.me/submissions/6608f3ff-ea04-40eb-adb8-58f72439203d

module
public import Definitions.Def_BalanceSpecificaton_OneSidedExample
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Theorems.Thm_BalanceSpecification_OneSidedExample_edge_selected

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (s : Vertex) (ds : List Bool) : ∃ t, Walk s (runWord s ds) t := by
  induction ds generalizing s with
  | nil => exact ⟨s, .nil s⟩
  | cons d ds ih =>
    obtain ⟨t, ht⟩ := ih (edgeTarget s d)
    exact ⟨t, .cons (edge_selected s d) ht⟩
end BalanceSpecification.OneSidedExample

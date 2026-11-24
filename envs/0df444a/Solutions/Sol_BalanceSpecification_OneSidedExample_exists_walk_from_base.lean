-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.exists_walk_from_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:16.747885+00:00
-- url     : https://prove2.me/submissions/fe6ee41b-daf4-413c-aabd-aa651da5d5ec

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Theorems.Thm_BalanceSpecification_OneSidedExample_ascending_from_base_walk
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_append


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (s : Vertex) : ∃ w, Walk (.p 0) w s := by
  cases s with
  | q n => exact ⟨_, ascending_from_base_walk n⟩
  | p n => exact ⟨_, (ascending_from_base_walk n).append (Walk.cons (.qb n) (.nil _))⟩
end BalanceSpecification.OneSidedExample

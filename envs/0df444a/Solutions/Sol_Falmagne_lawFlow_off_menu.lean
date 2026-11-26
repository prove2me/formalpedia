-- Prove2me | solution 1 for Falmagne.lawFlow_off_menu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:35.634103+00:00
-- url     : https://prove2.me/submissions/7d5efe84-b0f2-43eb-99b6-6644be37b79a

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Representation
public import Theorems.Thm_Falmagne_rankingEdge_eq_zero_of_not_mem
public import Theorems.Thm_Falmagne_mem_lowerContour
attribute [local simp] Falmagne.mem_lowerContour


attribute [local simp] Falmagne.rankingEdge_eq_zero_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
namespace Falmagne
theorem _root_.solution (w : RankingLaw X) (hx : x ∉ A) :
    lawFlow w x A = 0 := by
  simp [lawFlow, rankingEdge, hx]
end Falmagne

-- Prove2me | solution 1 for Falmagne.rankingEdge_eq_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:47.697473+00:00
-- url     : https://prove2.me/submissions/b240fe0a-43b9-42a8-8427-29e999db858c

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Representation
public import Theorems.Thm_Falmagne_mem_lowerContour
attribute [local simp] Falmagne.mem_lowerContour



set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
namespace Falmagne
theorem _root_.solution (hx : x ∉ A) :
    rankingEdge l x A = 0 := by simp [rankingEdge, hx]
end Falmagne

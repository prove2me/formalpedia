-- Prove2me | solution 1 for Falmagne.lowerContour_cons_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:26.923801+00:00
-- url     : https://prove2.me/submissions/7e489807-ca5c-4299-be74-adadde12effd

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_PathChoice
public import Theorems.Thm_Falmagne_mem_lowerContour
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_nil
public import Theorems.Thm_Falmagne_rankingEdge_eq_zero_of_not_mem
attribute [local simp] Falmagne.mem_lowerContour
attribute [local simp] Falmagne.pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil
attribute [local simp] Falmagne.rankingEdge_eq_zero_of_not_mem



set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {x y : X} {A : Finset X}
namespace Falmagne
theorem _root_.solution (hxy : x ≠ y) (hyn : y ∉ l) :
    lowerContour (y :: l) x = lowerContour l x := by
  ext z
  by_cases hz : z = y
  · subst z
    simp [lowerContour, hyn, List.idxOf_cons_ne l hxy.symm]
  · simp [lowerContour, hz, List.idxOf_cons_ne l hxy.symm, List.idxOf_cons_ne l (Ne.symm hz)]
end Falmagne

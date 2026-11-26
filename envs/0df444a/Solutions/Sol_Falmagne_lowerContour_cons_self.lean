-- Prove2me | solution 1 for Falmagne.lowerContour_cons_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:25.138242+00:00
-- url     : https://prove2.me/submissions/b929265f-ac2f-4d16-8676-b6f399e0212e

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
theorem _root_.solution (h : x ∉ l) :
    lowerContour (x :: l) x = (x :: l).toFinset := by
  ext y
  simp [lowerContour]
end Falmagne

-- Prove2me | solution 1 for Falmagne.pathFlow_eq_lowerContour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:11.910681+00:00
-- url     : https://prove2.me/submissions/9415ada7-cbbe-40c1-b64b-e488dc98dfa0

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_PathChoice
public import Theorems.Thm_Falmagne_lowerContour_cons_self
public import Theorems.Thm_Falmagne_lowerContour_cons_of_ne
public import Theorems.Thm_Falmagne_mem_lowerContour
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_nil
public import Theorems.Thm_Falmagne_pathFlow_zero_of_not_mem
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
theorem _root_.solution (hl : l.Nodup) (hx : x ∈ l) :
    pathFlow l x A = if A = lowerContour l x then 1 else 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
      obtain ⟨hyn, hln⟩ := List.nodup_cons.mp hl
      by_cases hxy : x = y
      · subst x
        rw [pathFlow_cons, pathFlow_zero_of_not_mem l hyn, add_zero,
          lowerContour_cons_self hyn]
        simp [unitEdge]
      · have hx' : x ∈ l := (List.mem_cons.mp hx).resolve_left hxy
        rw [pathFlow_cons, lowerContour_cons_of_ne hxy hyn, ih hln hx']
        simp [unitEdge, hxy]
end Falmagne

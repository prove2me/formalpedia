-- Prove2me | solution 1 for Falmagne.self_mem_lowerContour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:54.566078+00:00
-- url     : https://prove2.me/submissions/ef03edfb-34cd-4a12-902e-de9a1d1e0c4e

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Basic
public import Theorems.Thm_Falmagne_ranking_mem
public import Theorems.Thm_Falmagne_mem_lowerContour
attribute [local simp] Falmagne.mem_lowerContour

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x y : X}
namespace Falmagne
theorem _root_.solution (hl : IsRanking l) (x : X) :
    x ∈ lowerContour l x := by
  simp [ranking_mem hl x]
end Falmagne

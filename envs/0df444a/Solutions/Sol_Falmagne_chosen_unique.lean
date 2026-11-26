-- Prove2me | solution 1 for Falmagne.chosen_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:59.095277+00:00
-- url     : https://prove2.me/submissions/e744dba3-9054-449d-8877-f88836910101

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
theorem _root_.solution (hl : IsRanking l)
    (hx : x ∈ A ∧ A ⊆ lowerContour l x)
    (hy : y ∈ A ∧ A ⊆ lowerContour l y) : x = y := by
  have hxy := (mem_lowerContour l x y).mp (hx.2 hy.1) |>.2
  have hyx := (mem_lowerContour l y x).mp (hy.2 hx.1) |>.2
  exact (List.idxOf_inj (ranking_mem hl x)).mp (Nat.le_antisymm hxy hyx)
end Falmagne

-- Prove2me | solution 1 for Falmagne.lowerContour_subset_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:55.07731+00:00
-- url     : https://prove2.me/submissions/531fa065-7171-40fd-ae89-589996ac28e8

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
theorem _root_.solution (hl : IsRanking l) :
    A ⊆ lowerContour l x ↔ ∀ y ∈ A, l.idxOf x ≤ l.idxOf y := by
  constructor
  · intro h y hy
    exact (mem_lowerContour l x y).mp (h hy) |>.2
  · intro h y hy
    exact (mem_lowerContour l x y).mpr ⟨ranking_mem hl y, h y hy⟩
end Falmagne

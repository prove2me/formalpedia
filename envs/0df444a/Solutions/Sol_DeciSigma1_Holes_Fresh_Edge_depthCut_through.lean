-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Edge.depthCut_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:23.447284+00:00
-- url     : https://prove2.me/submissions/4c4c1ec4-a553-4eaa-a302-32da979a33e0

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_add_baseLen
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_firstBlocksLength_eq
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
open DeciSigma1.Holes.Fresh.Edge
variable {W : Fin k → List α} {t : ℕ} (e : Edge W t)
namespace DeciSigma1.Holes.Fresh.Edge
theorem _root_.solution {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (h : e.TraversedBy o) {d : ℕ} (hd : d ≤ e.endDepth) :
    depthCut W t o d + firstBlocksLength e.blocks.reverse d = o.2.2 := by
  rw [← e.firstBlocksLength_eq h hd]
  exact depthCut_add_baseLen ho (hd.trans (e.through_iff.mp h).1)
end DeciSigma1.Holes.Fresh.Edge

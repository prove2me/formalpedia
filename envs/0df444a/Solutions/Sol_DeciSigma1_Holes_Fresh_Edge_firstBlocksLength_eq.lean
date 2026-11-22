-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Edge.firstBlocksLength_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:55.169477+00:00
-- url     : https://prove2.me/submissions/548b9c94-0c1f-4b51-987d-96bd32f0864e

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
open DeciSigma1.Holes.Fresh.Edge
variable {W : Fin k → List α} {t : ℕ} (e : Edge W t)
namespace DeciSigma1.Holes.Fresh.Edge
theorem _root_.solution {o : Fin k × ℕ × ℕ} (h : e.TraversedBy o) {d : ℕ}
    (hd : d ≤ e.endDepth) :
    firstBlocksLength (reversedBlocks W t o) d = firstBlocksLength e.blocks.reverse d := by
  have h2 := (e.through_iff.mp h).2
  unfold firstBlocksLength
  rw [show (reversedBlocks W t o).take d = ((reversedBlocks W t o).take e.endDepth).take d by
      rw [List.take_take, Nat.min_eq_left hd],
    show e.blocks.reverse.take d = (e.blocks.reverse.take e.endDepth).take d by
      rw [List.take_take, Nat.min_eq_left hd], h2]
end DeciSigma1.Holes.Fresh.Edge

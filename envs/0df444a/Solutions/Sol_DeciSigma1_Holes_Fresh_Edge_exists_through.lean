-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Edge.exists_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:17.116145+00:00
-- url     : https://prove2.me/submissions/8acb99c5-d87c-47ce-b49f-3bb74dec717c

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_commonSuffixLength_self
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_endDepth_le_length

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
open DeciSigma1.Holes.Fresh.Edge
variable {W : Fin k → List α} {t : ℕ} (e : Edge W t)
namespace DeciSigma1.Holes.Fresh.Edge
theorem _root_.solution :
    ∃ o ∈ upperOccurrences W t, upperParse W t o = e.blocks ∧ e.TraversedBy o := by
  obtain ⟨o, ho, hZ⟩ := mem_image.mp e.blocks_mem
  refine ⟨o, ho, hZ, ?_⟩
  unfold TraversedBy
  rw [hZ, commonSuffixLength_self]
  exact e.endDepth_le_length
end DeciSigma1.Holes.Fresh.Edge

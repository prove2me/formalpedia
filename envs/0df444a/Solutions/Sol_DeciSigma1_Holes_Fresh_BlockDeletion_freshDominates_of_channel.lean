-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.freshDominates_of_channel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:50.243634+00:00
-- url     : https://prove2.me/submissions/bbfbf5f9-7e1f-4293-9147-7501dc6a7fe2

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_endState_apply
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_visitedStates_subset
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_fresh_apply

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    (hch : ∀ i j, T.channel m.apply i j ⊆ T.channel W i j) : FreshDominates T m.apply W :=
  ⟨⟨m.endState_apply, m.visitedStates_subset, hch⟩, m.fresh_apply hfr⟩
end DeciSigma1.Holes.Fresh.BlockDeletion

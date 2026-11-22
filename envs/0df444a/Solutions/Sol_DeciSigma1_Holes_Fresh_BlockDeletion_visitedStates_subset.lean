-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.visitedStates_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:33:59.16609+00:00
-- url     : https://prove2.me/submissions/62df3272-732a-4fc5-8d6a-710caf92be00

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_length_not_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_runPrefix_apply
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_visitedStates
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_mem_visitedStates
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_le_length


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
theorem _root_.solution [DecidableEq S] (l : Fin k) :
    T.visitedStates m.apply l ⊆ T.visitedStates W l := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Table.mem_visitedStates.mp hq
  rw [m.runPrefix_apply]
  exact Table.runPrefix_mem_visitedStates W l
    (greatestPreimage_le_length _ (m.length_not_mem_sitePositions l) ha)
end DeciSigma1.Holes.Fresh.BlockDeletion

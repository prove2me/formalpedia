-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.properVisitedStates_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:15.68155+00:00
-- url     : https://prove2.me/submissions/74722cf9-df0c-4e17-a775-fb6e4dcf4a4d

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_runPrefix_apply
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_properVisitedStates
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_lt_length


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
    T.properVisitedStates m.apply l ⊆ T.properVisitedStates W l := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Table.mem_properVisitedStates.mp hq
  rw [m.runPrefix_apply]
  exact Table.mem_properVisitedStates.mpr ⟨_, greatestPreimage_lt_length _ ha, rfl⟩
end DeciSigma1.Holes.Fresh.BlockDeletion

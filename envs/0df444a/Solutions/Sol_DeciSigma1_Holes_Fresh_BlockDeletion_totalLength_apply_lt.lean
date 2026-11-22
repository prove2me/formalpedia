-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.totalLength_apply_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:32:07.654279+00:00
-- url     : https://prove2.me/submissions/53e6b8de-79a1-4afc-8c4c-56a59a930672

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_delta_pos
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_mem_sites
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_valid
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_exists_through
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_le
public import Theorems.Thm_DeciSigma1_Words_retainedCount_lt_of_mem


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
theorem _root_.solution : totalLength m.apply < totalLength W := by
  obtain ⟨o, ho, -, hth⟩ := m.edge.exists_through
  have hsite : depthCut W t o m.maxDepth ∈ m.sites o.1 := m.mem_sites.mpr ⟨o, ho, rfl, hth, rfl⟩
  have hd := m.delta_pos
  unfold totalLength
  apply Finset.sum_lt_sum
  · intro l _
    rw [apply, length_deletePositions]
    exact retainedCount_le _
  · refine ⟨o.1, mem_univ _, ?_⟩
    rw [apply, length_deletePositions]
    exact retainedCount_lt_of_mem
      (mem_sitePositions.mpr ⟨_, hsite, le_rfl, by omega⟩)
      (by have := (m.site_valid hsite).2.1; omega)
end DeciSigma1.Holes.Fresh.BlockDeletion

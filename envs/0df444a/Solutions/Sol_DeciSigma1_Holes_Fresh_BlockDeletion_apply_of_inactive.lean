-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.apply_of_inactive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:41.814562+00:00
-- url     : https://prove2.me/submissions/fc013017-1aca-40b9-9261-af1f045df758

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_active_of_through
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_occ
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_empty



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution {l : Fin k} (hl : l ∉ active W (t + 1)) :
    m.sites l = ∅ ∧ m.apply l = W l := by
  have h : m.sites l = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro c hc
    obtain ⟨o, ho, hol, hth, -⟩ := m.site_occ hc
    exact hl (hol ▸ m.active_of_through ho hth)
  refine ⟨h, ?_⟩
  rw [BlockDeletion.apply, h]
  exact deletePositions_empty _
end DeciSigma1.Holes.Fresh.BlockDeletion

-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.upperCutLength_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:25.612852+00:00
-- url     : https://prove2.me/submissions/adad7539-5fca-4162-a487-86d486a8f50f

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_minDepth_le_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_depthCut_through


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
theorem _root_.solution {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : m.edge.TraversedBy o) :
    depthCut W t o m.minDepth + m.upperCutLength = o.2.2 ∧ depthCut W t o m.maxDepth +
        m.deletionLength +
        m.upperCutLength = o.2.2 ∧
      0 < m.upperCutLength := by
  have h1 := m.edge.depthCut_through ho hth m.minDepth_le_endDepth
  have h2 := m.site_spec ho hth
  refine ⟨h1, by unfold upperCutLength; omega, by unfold upperCutLength; omega⟩
end DeciSigma1.Holes.Fresh.BlockDeletion

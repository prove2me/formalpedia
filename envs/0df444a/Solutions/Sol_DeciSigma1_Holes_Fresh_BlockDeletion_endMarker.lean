-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.endMarker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:33:11.52421+00:00
-- url     : https://prove2.me/submissions/70641d4d-8946-42fd-937b-0b5fb6bf32ac

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_minDepth_le_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_upperCutLength_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_active_of_through
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_active_t_of_through
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_card_depthCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_depthCut_anti
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_deletionMargin_gt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_maxDepth_lt_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_eq_contextAnchors
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_anchors_Ioc_marker_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_upperOcc
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


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
theorem _root_.solution [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o) :
    ∃ g ∈ active W (t + 1), marker W (t + 1) g <:+ (W o.1).take o.2.2 ∧
      (marker W (t + 1) g).length ≤ m.upperCutLength := by
  have hact := m.active_of_through ho hth
  have hE := (mem_upperOcc.mp ho).2.1
  rw [anchors_eq_contextAnchors hact] at hE
  obtain ⟨-, g, hg, hs⟩ := (mem_contextAnchors_succ W).mp hE
  refine ⟨g, hg, hs, Nat.le_of_not_lt fun hlong => ?_⟩
  have hEl := (upperOcc_spec ho).2.1
  obtain ⟨hl1, hocc⟩ := (suffix_take_iff hEl).mp hs
  have hsp := card_anchors_Ioc_marker_le hfr t hg (W o.1) hocc
  have hnt := m.upperCutLength_spec ho hth
  have hbn := (m.edge.through_iff.mp hth).1
  have hin : m.minDepth ≤ lowerBlockCount W t o := by have := m.minDepth_le_endDepth; omega
  have hctx := anchors_eq_contextAnchors (m.active_t_of_through ho hth)
  have := card_depthCuts ho hin (X := (contextAnchors W t (W o.1)).filter
    (fun p => o.2.2 - (marker W (t + 1) g).length < p ∧
      p ≤ o.2.2 - (marker W (t + 1) g).length + (marker W (t + 1) g).length)) (by
    intro d hd
    rw [mem_filter, ← hctx]
    have h1 := depthCut_anti ho hd hin
    have h2 := depthCut_anti ho (Nat.zero_le d) (hd.trans hin)
    obtain ⟨hall, -⟩ := depthCut_spec ho
    have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth
    exact ⟨(hall d (by omega)).1, by rw [show depthCut W t o 0 = o.2.2 from rfl] at h2; omega,
      by rw [show depthCut W t o 0 = o.2.2 from rfl] at h2; omega⟩)
  have := m.deletionMargin_gt m.left_margin
  omega
end DeciSigma1.Holes.Fresh.BlockDeletion

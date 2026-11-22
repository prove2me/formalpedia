-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.compatible_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:28.294912+00:00
-- url     : https://prove2.me/submissions/49ab6dff-c240-48a1-bfd0-1e056d38ba05

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_contextAnchors_anti
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_windowLength_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_card_depthCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_deletionMargin_gt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_depthCut_anti
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_maxDepth_lt_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_minDepth_le_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_order
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_strictlySeparated
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_StrictlySeparated_lt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_anchors_inside_marker_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_of_mem_anchors_of_lt_length
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
    {l : Fin k} {c c₂ : ℕ} (hc : c ∈ m.sites l) (hc₂ : c₂ ∈ m.sites l) (hlt : c₂ < c) :
    c₂ + m.deletionLength + windowLength W t (W l) c ≤ c := by
  have hs := m.strictlySeparated l
  have hsep := hs.lt hc₂ hc hlt
  rcases Nat.eq_zero_or_pos (windowLength W t (W l) c) with hw0 | hwpos
  · omega
  obtain ⟨r, hr1, hrt, g, hg, hμ, hlen⟩ := windowLength_spec hwpos
  refine Nat.le_of_not_lt fun hcon => ?_
  obtain ⟨o, ho, hol, hth, hoc⟩ := m.site_occ hc
  obtain ⟨o₂, ho₂, hol₂, hth₂, hoc₂⟩ := m.site_occ hc₂
  have hord := m.site_order ho₂ ho hth₂ hth (hol₂.trans hol.symm) (by rw [hoc, hoc₂]; exact hlt)
  have hsp := m.site_spec ho hth
  have hsp₂ := m.site_spec ho₂ hth₂
  rw [hoc] at hsp
  rw [hoc₂] at hsp₂
  have hcW : c ≤ (W l).length := by rw [← hol]; omega
  obtain ⟨hl1, hocc⟩ := (suffix_take_iff hcW).mp hμ
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hspan := card_anchors_inside_marker_le hfr r' hg (W l) hocc
  have hin : m.minDepth ≤ lowerBlockCount W t o₂ := by
    have := m.minDepth_le_endDepth; have := (m.edge.through_iff.mp hth₂).1; omega
  have hin' : m.minDepth < lowerBlockCount W t o₂ := by
    have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth; have :=
        (m.edge.through_iff.mp hth₂).1; omega
  have hdi : depthCut W t o₂ m.minDepth = c₂ + m.deletionLength := by omega
  have := card_depthCuts ho₂ hin (X := (contextAnchors W r' (W l)).filter
    (fun p => c - (marker W (r' + 1) g).length < p ∧
      p < c - (marker W (r' + 1) g).length + (marker W (r' + 1) g).length)) (by
    intro d hd
    rw [mem_filter]
    have h1 := depthCut_anti ho₂ hd hin
    have h2 := depthCut_anti ho₂ (Nat.zero_le d) (hd.trans hin)
    rw [show depthCut W t o₂ 0 = o₂.2.2 from rfl] at h2
    obtain ⟨hall, -⟩ := depthCut_spec ho₂
    have hA := (hall d (by omega)).1
    have hEl := (upperOcc_spec ho₂).2.1
    rw [hol₂] at hA hEl
    refine
        ⟨contextAnchors_anti (by omega) _ (mem_contextAnchors_of_mem_anchors_of_lt_length hA
            (by omega)), by omega,
      by omega⟩)
  have := m.deletionMargin_gt m.left_margin
  omega
end DeciSigma1.Holes.Fresh.BlockDeletion

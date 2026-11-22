-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:48.348552+00:00
-- url     : https://prove2.me/submissions/7937ad46-4490-48ba-9209-72faaf62b174

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_card_depthCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_deletionMargin_gt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_depthCut_anti
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_maxDepth_lt_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_minDepth_le_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_active_succ_subset
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_eq_contextAnchors
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_anchors_Ioc_marker_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_occ_of_suffix
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
theorem _root_.solution [DecidableEq S] (hfr : ∀ i, T.Fresh W i) {l : Fin k}
    (hl : l ∈ active W (t + 1)) {c : ℕ} (hc : c ∈ m.sites l) :
    c + m.deletionLength + (marker W (t + 1) l).length ≤ (W l).length := by
  obtain ⟨o, ho, rfl, hth, hoc⟩ := m.site_occ hc
  have hsp := m.site_spec ho hth
  rw [hoc] at hsp
  refine Nat.le_of_not_lt fun hcon => ?_
  have hσ := marker_suffix W (t + 1) o.1
  have hocc : marker W (t + 1) o.1 <+:
      (W o.1).drop ((W o.1).length - (marker W (t + 1) o.1).length) := occ_of_suffix hσ
  have hspan := card_anchors_Ioc_marker_le hfr t hl (W o.1) hocc
  have hσl := hσ.length_le
  have hin : m.minDepth ≤
      lowerBlockCount W t o := by have := m.minDepth_le_endDepth;
                                  have := (m.edge.through_iff.mp hth).1; omega
  have hin' : m.minDepth < lowerBlockCount W t o := by
    have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth; have :=
        (m.edge.through_iff.mp hth).1; omega
  have hctx := anchors_eq_contextAnchors (active_succ_subset W t hl)
  have hdi : depthCut W t o m.minDepth = c + m.deletionLength := by omega
  have := card_depthCuts ho hin (X := (contextAnchors W t (W o.1)).filter
    (fun p => (W o.1).length - (marker W (t + 1) o.1).length < p ∧
      p ≤ (W o.1).length - (marker W (t + 1) o.1).length + (marker W (t + 1) o.1).length)) (by
    intro d hd
    rw [mem_filter, ← hctx]
    have h1 := depthCut_anti ho hd hin
    have h2 := depthCut_anti ho (Nat.zero_le d) (hd.trans hin)
    obtain ⟨hall, -⟩ := depthCut_spec ho
    rw [show depthCut W t o 0 = o.2.2 from rfl] at h2
    refine ⟨(hall d (by omega)).1, by omega, by omega⟩)
  have := m.deletionMargin_gt m.left_margin
  omega
end DeciSigma1.Holes.Fresh.BlockDeletion

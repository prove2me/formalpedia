-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Edge.marker_fits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:36:11.884811+00:00
-- url     : https://prove2.me/submissions/5b6e95e1-3e2d-4121-bf58-efd789290a5e

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_anti
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_bounds
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_contextAnchors_anti
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_split
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_anchors_Ioc_marker_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt_of_lt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
namespace Edge
theorem _root_.solution (hfr : ∀ i, T.Fresh W i)
    {t : ℕ} (e : Edge W t) {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : e.TraversedBy o) {p : ℕ} (hp0 : 0 < p)
    (hp : p + deletionMargin k (Fintype.card S) ≤ e.endDepth)
    {r : ℕ} (hr : 1 ≤ r) (hrt : r ≤ t) {m : Fin k} (hm : m ∈ active W r)
    (hs : marker W r m <:+ (W o.1).take (depthCut W t o p)) :
    (marker W r m).length ≤ depthCut W t o p - depthCut W t o e.endDepth := by
  have hM : k * (Fintype.card S - 1) + 2 < deletionMargin k (Fintype.card S) := by
    unfold deletionMargin; omega
  have hb := (e.through_iff.mp hth).1
  have hpb : p < e.endDepth := by omega
  have hpN : p < lowerBlockCount W t o := by omega
  have hcp := (depthCut_spec ho).1 p hpN
  have hcb := depthCut_bounds ho hb
  have hle := (depthCut_lt_of_lt ho hpb hb).le
  have hce : depthCut W t o p < o.2.2 := by
    have hh := depthCut_lt_of_lt ho hp0 (by omega : p ≤ lowerBlockCount W t o)
    simpa only [depthCut, depthCutAt] using hh
  have hword := (upperOcc_spec ho).2.1
  have hsplit := anchorCount_split (A := anchors W t o.1) hle hcp.2.2.1
  have hcntb : anchorCount (anchors W t o.1) (depthCut W t o e.endDepth) o.2.2 = e.endDepth := by
    rcases lt_or_eq_of_le hb with hh | hh
    · exact ((depthCut_spec ho).1 e.endDepth hh).2.2.2
    · rw [hh, (depthCut_spec ho).2]; rfl
  have hcount : anchorCount (anchors W t o.1) (depthCut W t o e.endDepth) (depthCut W t o p) =
      e.endDepth - p := by
    omega
  have hlen := hs.length_le
  simp only [List.length_take] at hlen
  have hoM := (suffix_take_iff (hcp.2.2.1.trans hword)).mp hs
  by_contra hbad
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hspan := card_anchors_Ioc_marker_le hfr r' hm (W o.1) hoM.2
  rw [Nat.sub_add_cancel hoM.1] at hspan
  have hsub : (anchors W t o.1).filter
      (fun q => depthCut W t o e.endDepth < q ∧ q ≤ depthCut W t o p) ⊆
      (contextAnchors W r' (W o.1)).filter
        (fun q => depthCut W t o p - (marker W (r' + 1) m).length < q ∧
          q ≤ depthCut W t o p) := by
    intro q hq
    obtain ⟨hq, hq1, hq2⟩ := mem_filter.mp hq
    have hctx : q ∈ contextAnchors W t (W o.1) := by
      rcases mem_insert.mp hq with hh | hh
      · omega
      · exact hh
    exact mem_filter.mpr ⟨contextAnchors_anti (by omega : r' ≤ t) _ hctx, by omega, hq2⟩
  have := card_le_card hsub
  unfold anchorCount at hcount
  omega
end Edge
end DeciSigma1.Holes.Fresh

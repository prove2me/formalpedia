-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:46.034377+00:00
-- url     : https://prove2.me/submissions/1c48585b-f64b-451c-b61f-1a77b518ad32

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_upperCutLength_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_endMarker
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_anchor_ne_site
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_junction_window
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_traversedBy_of_text_eq
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_contextAnchors_apply
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_delta_pos
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_mem_sites
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_strictlySeparated
public import Theorems.Thm_DeciSigma1_Holes_Fresh_greatestPreimage_add_eq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_length_of_mem_anchors
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_upperOcc
public import Theorems.Thm_DeciSigma1_Holes_Fresh_retainedCount_site_right
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_drop_deleteSites
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
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {l₁ l₂ : Fin k} {u₁ u₂ : ℕ} (hJ : IsJunction m.deletionLength (m.sites l₁) u₁)
    (htext : ((m.apply l₁).drop u₁).take m.upperCutLength =
        ((m.apply l₂).drop u₂).take m.upperCutLength)
    (hfree : ∀ J,
        IsJunction m.deletionLength (m.sites l₂) J → ¬ (u₂ < J ∧ J < u₂ + m.upperCutLength))
    (hlen : u₂ + m.upperCutLength ≤ (m.apply l₂).length) :
    IsJunction m.deletionLength (m.sites l₂) u₂ := by
  obtain ⟨c₁, hc₁, rfl⟩ := hJ
  obtain ⟨o₁, ho₁, hol₁, hth₁, hoc₁⟩ := m.site_occ hc₁
  obtain ⟨-, -, -, hwin₁⟩ := m.junction_window hc₁
  obtain ⟨hnt1, hnt2, hnpos⟩ := m.upperCutLength_spec ho₁ hth₁
  obtain ⟨g, hg, hσE, hσl⟩ := m.endMarker hfr ho₁ hth₁
  rw [hoc₁] at hnt2
  have hE₁ := (upperOcc_spec ho₁).2.1
  rw [hol₁] at hE₁ hσE
  have hσz : marker W (t + 1) g <:+
      ((W l₁).drop (c₁ + m.deletionLength)).take m.upperCutLength := by
    have hcat : (W l₁).take o₁.2.2 =
        (W l₁).take (c₁ + m.deletionLength) ++
            ((W l₁).drop (c₁ + m.deletionLength)).take m.upperCutLength := by
      rw [← List.take_add]; congr 1; omega
    rw [hcat] at hσE
    exact List.suffix_of_suffix_length_le hσE (List.suffix_append _ _) (by simp; omega)
  have hσU : marker W (t + 1) g <:+ (m.apply l₂).take (u₂ + m.upperCutLength) := by
    rw [List.take_add, ← htext, hwin₁]
    exact hσz.trans (List.suffix_append _ _)
  have hanc : u₂ + m.upperCutLength ∈ contextAnchors W (t + 1) (m.apply l₂) :=
    (mem_contextAnchors_succ W).mpr ⟨hlen, g, hg, hσU⟩
  obtain ⟨p₂, hp₂, hret, hkp⟩ :=
      (m.contextAnchors_apply (r := t + 1) (by omega) le_rfl l₂ _).mp hanc
  have hp₂A : p₂ ∈ anchors W (t + 1) l₂ := mem_insert_of_mem hp₂
  have hs := m.strictlySeparated l₂
  have hδ := m.delta_pos
  have hka : greatestPreimage (sitePositions m.deletionLength (m.sites l₂)) u₂ + m.upperCutLength =
      p₂ :=
    greatestPreimage_add_eq hnpos hfree hret (fun c hc => (m.anchor_ne_site hp₂A hc).2) hkp
  have hwin₂ : ((m.apply l₂).drop u₂).take m.upperCutLength =
      ((W l₂).drop (greatestPreimage (sitePositions m.deletionLength (m.sites l₂)) u₂)).take
        m.upperCutLength :=
    take_drop_deleteSites _ hfree
  have hz₂ : ((W l₂).drop (p₂ - m.upperCutLength)).take m.upperCutLength =
      ((W o₁.1).drop (o₁.2.2 - m.upperCutLength)).take m.upperCutLength := by
    rw [show p₂ - m.upperCutLength =
          greatestPreimage (sitePositions m.deletionLength (m.sites l₂)) u₂ by omega,
        ← hwin₂,
        ← htext, hwin₁,
      hol₁, show o₁.2.2 - m.upperCutLength = c₁ + m.deletionLength by omega]
  have hthr := m.traversedBy_of_text_eq hfr ho₁ hth₁ hp₂A (by omega) hz₂
  have hl₂ : W l₂ ≠ [] :=
    List.ne_nil_of_length_pos (by have := le_length_of_mem_anchors hp₂A; omega)
  have ho₂ : (l₂, upperOccurrenceStart W t l₂ p₂, p₂) ∈ upperOccurrences W t :=
      mem_upperOcc.mpr ⟨hl₂, hp₂A, rfl⟩
  obtain ⟨-, hn2', -⟩ := m.upperCutLength_spec ho₂ hthr
  have hE2 : (l₂, upperOccurrenceStart W t l₂ p₂, p₂).2.2 = p₂ := rfl
  rw [hE2] at hn2'
  have hc₂ : depthCut W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂) m.maxDepth ∈ m.sites l₂ :=
    m.mem_sites.mpr ⟨_, ho₂, rfl, hthr, rfl⟩
  refine ⟨_, hc₂, ?_⟩
  rw [← retainedCount_site_right hc₂, show depthCut W t (l₂, upperOccurrenceStart W t l₂ p₂,
      p₂) m.maxDepth + m.deletionLength =
    greatestPreimage (sitePositions m.deletionLength (m.sites l₂)) u₂ by omega]
  exact retainedCount_greatestPreimage u₂
end DeciSigma1.Holes.Fresh.BlockDeletion

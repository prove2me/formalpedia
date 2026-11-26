-- Prove2me | solution 1 for GallaiEdmonds.maximumMatching_structure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:49.236462+00:00
-- url     : https://prove2.me/submissions/7c14f583-0016-42fb-8657-7ce4b50ed8a8

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_setD_eq
public import Theorems.Thm_GallaiEdmonds_setA_eq
public import Theorems.Thm_GallaiEdmonds_mem_setC_iff
public import Theorems.Thm_GallaiEdmonds_compSet_mk
public import Theorems.Thm_GallaiEdmonds_compSet_mem_oddComps
public import Theorems.Thm_GallaiEdmonds_IsBarrier_eq
public import Theorems.Thm_GallaiEdmonds_cc_eq_of_mem
public import Theorems.Thm_GallaiEdmonds_cc_subset
public import Theorems.Thm_GallaiEdmonds_exists_minBarrier
public import Theorems.Thm_GallaiEdmonds_step1


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    (∀ v ∈ setC G, ∃ w ∈ setC G, M.Adj v w) ∧
    (∀ a ∈ setA G, ∃ u ∈ setD G, M.Adj a u) ∧
    (∀ a ∈ setA G, ∀ a' ∈ setA G, ∀ u u' : ↥(setD G), a ≠ a' → M.Adj a u → M.Adj a' u' →
      (G.induce (setD G)).connectedComponentMk u ≠
        (G.induce (setD G)).connectedComponentMk u') ∧
    (∀ c : (G.induce (setD G)).ConnectedComponent, ∀ v ∈ compSet G c, ∀ w ∈ compSet G c,
      v ≠ w → (∃ x ∈ compSet G c, M.Adj v x) ∨ (∃ x ∈ compSet G c, M.Adj w x)) := by
  obtain ⟨U, hU⟩ := exists_minBarrier G
  obtain ⟨h1a, h1b, h1c, h1d⟩ := step1 hM.1 (hU.1.eq hM.1 hM.2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    have hv' := (mem_setC_iff G hU v).1 hv
    obtain ⟨z, hz, hadj⟩ := h1d v hv'.1 hv'.2
    exact ⟨z, (mem_setC_iff G hU z).2 ⟨cc_subset hz, by rw [cc_eq_of_mem hz]; exact hv'.2⟩,
      hadj⟩
  · intro a ha
    rw [setA_eq G hU] at ha
    obtain ⟨x, hx, hxU, hodd⟩ := h1a a ha
    exact ⟨x, by rw [setD_eq G hU]; exact ⟨hxU, hodd⟩, hx⟩
  · intro a ha a' ha' u u' hne hu hu' heq
    rw [setA_eq G hU] at ha ha'
    have h1 := compSet_mk G hU u.1 u.2
    have h2 := compSet_mk G hU u'.1 u'.2
    simp only [Subtype.coe_eta] at h1 h2
    rw [heq, h2] at h1
    exact h1b a ha a' ha' u u' hne hu hu' h1.symm
  · intro c v hv w hw hne
    exact h1c _ (compSet_mem_oddComps G hU c) v hv w hw hne
end GallaiEdmonds

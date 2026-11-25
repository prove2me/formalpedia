-- Prove2me | solution 1 for ChromaticReconstruction.phiTerm_inr_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:24:37.926804+00:00
-- url     : https://prove2.me/submissions/664654a8-958a-421f-a33b-ae73d8ea352e

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_mem_extEdges_inl_inl
import Theorems.Thm_ChromaticReconstruction_mem_extEdges_inl_inr
import Theorems.Thm_ChromaticReconstruction_mem_extEdges_inr_inl
import Theorems.Thm_ChromaticReconstruction_not_mem_extEdges_inr_inr
import Theorems.Thm_ChromaticReconstruction_singleton_inr_mem_compSets
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_phiTerm_eq_zero_of_isolated
import Theorems.Thm_ChromaticReconstruction_singleton_mem_compSets_iff
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
namespace ChromaticReconstruction
theorem _root_.solution {A : Finset (Sym2 (K ⊕ Σ i, Fin (m i)))}
    (hA : A ⊆ (leafExt S m).edgeFinset) (l0 : Σ i, Fin (m i))
    (hnot : A ∉ S.edgeFinset.powerset.image (extEdges m l0)) : phiTerm A (.inr l0) = 0 := by
  by_cases h0 : leafEdge m l0 ∈ A
  · unfold phiTerm
    rw [if_neg]
    intro h
    rw [singleton_mem_compSets_iff] at h
    have := h (.inl l0.1) (by rw [leafEdge, Sym2.eq_swap] at h0; exact h0)
    simp at this
  by_cases h1 : ∃ l ≠ l0, leafEdge m l ∉ A
  · obtain ⟨l, hl, hlA⟩ := h1
    exact phiTerm_eq_zero_of_isolated (by simpa using hl) (singleton_inr_mem_compSets hA hlA)
  push_neg at h1
  exfalso
  apply hnot
  have hE : ∀ {z}, z ∈ A → z ∈ (leafExt S m).edgeSet := fun hz => by
    have := hA hz; rwa [SimpleGraph.mem_edgeFinset] at this
  refine mem_image.2 ⟨S.edgeFinset.filter (fun e => Sym2.map Sum.inl e ∈ A),
    by simp [filter_subset], ?_⟩
  ext z
  induction z using Sym2.ind with
  | _ a b =>
    rcases a with a | la <;> rcases b with b | lb
    · rw [mem_extEdges_inl_inl]
      simp only [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Sym2.map_pair_eq, and_iff_right_iff_imp]
      intro h
      simpa [SimpleGraph.mem_edgeSet] using hE h
    · rw [mem_extEdges_inl_inr]
      constructor
      · rintro ⟨rfl, hne⟩
        exact h1 lb hne
      · intro h
        have h' := hE h
        rw [SimpleGraph.mem_edgeSet, leafExt_adj_inl_inr] at h'
        refine ⟨h', ?_⟩
        rintro rfl
        exact h0 (by rw [leafEdge, h']; exact h)
    · rw [mem_extEdges_inr_inl]
      constructor
      · rintro ⟨rfl, hne⟩
        have := h1 la hne
        rw [leafEdge, Sym2.eq_swap] at this
        exact this
      · intro h
        have h' := hE h
        rw [SimpleGraph.mem_edgeSet, leafExt_adj_inr_inl] at h'
        refine ⟨h', ?_⟩
        rintro rfl
        exact h0 (by rw [leafEdge, h', Sym2.eq_swap]; exact h)
    · constructor
      · intro h
        exact absurd h not_mem_extEdges_inr_inr
      · intro h
        exact absurd (by simpa [SimpleGraph.mem_edgeSet] using hE h) id
end ChromaticReconstruction

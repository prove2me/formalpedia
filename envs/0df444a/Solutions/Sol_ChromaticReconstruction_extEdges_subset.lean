-- Prove2me | solution 1 for ChromaticReconstruction.extEdges_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:33.839387+00:00
-- url     : https://prove2.me/submissions/65803c12-21f1-4361-ba05-84676124b644

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_leafEdge_mem_edgeSet
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
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
theorem _root_.solution {l0 : Σ i, Fin (m i)} {F : Finset (Sym2 K)} (hF : F ⊆ S.edgeFinset) :
    extEdges m l0 F ⊆ (leafExt S m).edgeFinset := by
  intro z hz
  rw [SimpleGraph.mem_edgeFinset]
  simp only [extEdges, mem_union, mem_image, mem_erase, mem_univ, and_true, mem_map] at hz
  rcases hz with ⟨l, _, rfl⟩ | ⟨e, he, rfl⟩
  · exact leafEdge_mem_edgeSet l
  · have := hF he
    rw [SimpleGraph.mem_edgeFinset] at this
    induction e using Sym2.ind with
    | _ a b => simpa [SimpleGraph.mem_edgeSet] using this
end ChromaticReconstruction

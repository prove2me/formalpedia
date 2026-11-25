-- Prove2me | solution 1 for ChromaticReconstruction.not_mem_extEdges_inr_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:47:52.32874+00:00
-- url     : https://prove2.me/submissions/379a69b3-3a9b-49fb-b3bd-315d1a046c0e

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
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
theorem _root_.solution {l0 : Σ i, Fin (m i)} {F : Finset (Sym2 K)}
    {l l' : Σ i, Fin (m i)} : s(.inr l, .inr l') ∉ extEdges m l0 F := by
  simp only [extEdges, leafEdge, mem_union, mem_image, mem_erase, mem_univ, and_true, mem_map,
    not_or, not_exists, not_and]
  refine ⟨fun l'' _ h => ?_, fun z _ hz => ?_⟩
  · rw [Sym2.eq_iff] at h; simp at h
  · induction z using Sym2.ind with
    | _ c d => simp at hz
end ChromaticReconstruction

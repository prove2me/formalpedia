-- Prove2me | solution 1 for ChromaticReconstruction.mem_extEdges_inl_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:41:40.420343+00:00
-- url     : https://prove2.me/submissions/7dbe9adf-f41e-429c-ba14-8cc98577005c

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
theorem _root_.solution {l0 : Σ i, Fin (m i)} {F : Finset (Sym2 K)} {a b : K} :
    s(.inl a, .inl b) ∈ extEdges m l0 F ↔ s(a, b) ∈ F := by
  simp only [extEdges, leafEdge, mem_union, mem_image, mem_erase, mem_univ, and_true, mem_map]
  constructor
  · rintro (⟨l', _, h⟩ | ⟨z, hz, h⟩)
    · rw [Sym2.eq_iff] at h; simp at h
    · have : z = s(a, b) := Sym2.map.injective Sum.inl_injective (by simpa using h)
      exact this ▸ hz
  · intro h
    exact Or.inr ⟨s(a, b), h, by simp⟩
end ChromaticReconstruction

-- Prove2me | solution 1 for ChromaticReconstruction.mem_extEdges_inl_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:42:27.912508+00:00
-- url     : https://prove2.me/submissions/0d5d21c9-a029-49e4-89d7-0db92bedf5c4

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
theorem _root_.solution {l0 : Σ i, Fin (m i)} {F : Finset (Sym2 K)} {a : K}
    {l : Σ i, Fin (m i)} :
    s(.inl a, .inr l) ∈ extEdges m l0 F ↔ l.1 = a ∧ l ≠ l0 := by
  simp only [extEdges, leafEdge, mem_union, mem_image, mem_erase, mem_univ, and_true, mem_map]
  constructor
  · rintro (⟨l', hl', h⟩ | ⟨z, _, hz⟩)
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [Sum.inl.injEq, Sum.inr.injEq] at h1 h2
        subst h1 h2; exact ⟨rfl, hl'⟩
      · simp at h1
    · induction z using Sym2.ind with
      | _ c d => simp at hz
  · rintro ⟨rfl, hl⟩
    exact Or.inl ⟨l, hl, rfl⟩
end ChromaticReconstruction

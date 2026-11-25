-- Prove2me | solution 1 for ChromaticReconstruction.famTree_degree_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:29:28.233565+00:00
-- url     : https://prove2.me/submissions/cc04859d-0932-4ea0-847b-9d7375013de9

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_CountingLower
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {r m : ℕ} {A : Finset ℕ} (hr : m + 2 ≤ r) {i : ℕ} (hi : 1 ≤ i)
    (him : i ≤ m) : (∃ v, (famTree r A).degree v = i + 1) ↔ i ∈ A := by
  constructor
  · rintro ⟨v, hv⟩
    rcases v with (u | ⟨u, j⟩) | l
    · rw [famTree, leafExt_degree_inl, starTree, leafExt_degree_inl] at hv
      simp [famWeights] at hv
      omega
    · rw [famTree, leafExt_degree_inl, starTree, leafExt_degree_inr] at hv
      simp only [famWeights] at hv
      split_ifs at hv with hj
      · have : (j : ℕ) = i := by omega
        rwa [← this]
      · omega
    · rw [famTree, leafExt_degree_inr] at hv
      omega
  · intro hiA
    refine ⟨.inl (.inr ⟨(), ⟨i, by omega⟩⟩), ?_⟩
    rw [famTree, leafExt_degree_inl, starTree, leafExt_degree_inr]
    simp [famWeights, hiA]
    omega
end ChromaticReconstruction

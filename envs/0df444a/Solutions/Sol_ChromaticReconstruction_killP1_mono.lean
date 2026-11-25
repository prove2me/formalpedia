-- Prove2me | solution 1 for ChromaticReconstruction.killP1_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:42.9408+00:00
-- url     : https://prove2.me/submissions/3381f064-ea84-45b7-aeef-d4be89c8dda1

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_killP1_X_of_ne
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_prod_X_multiset
import Theorems.Thm_ChromaticReconstruction_theta_mk
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.pairMS_mk
attribute [local simp] ChromaticReconstruction.pairSum_mk
attribute [local simp] ChromaticReconstruction.theta_mk



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (μ : Multiset ℕ) : killP1 (mono μ) = if 1 ∈ μ then 0 else mono μ := by
  unfold mono
  rw [← prod_X_multiset, map_multiset_prod, Multiset.map_map]
  split_ifs with h
  · apply Multiset.prod_eq_zero
    exact Multiset.mem_map.2 ⟨1, h, by simp⟩
  · congr 1
    apply Multiset.map_congr rfl
    intro r hr
    simp only [Function.comp_apply]
    exact killP1_X_of_ne (fun h' => h (h' ▸ hr))
end ChromaticReconstruction

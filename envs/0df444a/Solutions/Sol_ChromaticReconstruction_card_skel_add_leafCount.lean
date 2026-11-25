-- Prove2me | solution 1 for ChromaticReconstruction.card_skel_add_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:03:03.791135+00:00
-- url     : https://prove2.me/submissions/6eb19063-f936-49f1-81e8-1b3f8cef9030

import Definitions.Def_RequestProject_WeightedIso
import Definitions.Def_RequestProject_ProperTree
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
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
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V] {T : SimpleGraph V}
namespace ChromaticReconstruction
theorem _root_.solution (hT : IsProperTree T) :
    Fintype.card (SkelVert T) + ∑ c, leafCount T c = Fintype.card V := by
  rw [← Fintype.card_congr (properIso hT).toEquiv, Fintype.card_sum, Fintype.card_sigma]
  simp
end ChromaticReconstruction

-- Prove2me | solution 1 for ChromaticReconstruction.compSets_edgeSet_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:47:51.39752+00:00
-- url     : https://prove2.me/submissions/71687040-c2bc-4968-a912-9dd30cbd3d78

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_compSets_eq_image_compOf
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
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {G : SimpleGraph V} (hG : G.Connected) :
    compSets G.edgeSet = {univ} := by
  obtain ⟨v⟩ := hG.nonempty
  rw [compSets_eq_image_compOf]
  have : ∀ x, compOf G.edgeSet x = univ := by
    intro x
    ext y
    simp only [compOf, mem_filter, mem_univ, true_and, iff_true, SimpleGraph.fromEdgeSet_edgeSet]
    exact hG.preconnected x y
  rw [show compOf G.edgeSet = fun _ => univ from funext this]
  exact image_const ⟨v, mem_univ v⟩ univ
end ChromaticReconstruction

-- Prove2me | solution 1 for ChromaticReconstruction.card_le_two_of_adj_leaves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:56:51.307319+00:00
-- url     : https://prove2.me/submissions/d70bfcc1-7528-4664-9be7-f374c8a8f575

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_neighborFinset_eq_of_degree_one
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_mem_of_reachable_of_closed
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
variable {K : Type*} [Fintype K] {S : SimpleGraph K}
namespace ChromaticReconstruction
theorem _root_.solution (hS : S.Connected) {x y : K} (hxy : S.Adj x y)
    (hx : S.degree x = 1) (hy : S.degree y = 1) : Fintype.card K ≤ 2 := by
  have hclosed : ∀ u ∈ ({x, y} : Set K), ∀ z, s(u, z) ∈ S.edgeSet → z ∈ ({x, y} : Set K) := by
    intro u hu z hz
    rw [SimpleGraph.mem_edgeSet] at hz
    rcases hu with rfl | rfl
    · have := (S.mem_neighborFinset _ _).2 hz
      rw [neighborFinset_eq_of_degree_one hx hxy, mem_singleton] at this
      simp [this]
    · have := (S.mem_neighborFinset _ _).2 hz
      rw [neighborFinset_eq_of_degree_one hy hxy.symm, mem_singleton] at this
      simp [this]
  have hall : ∀ z, z ∈ ({x, y} : Finset K) := by
    intro z
    have hr : (SimpleGraph.fromEdgeSet S.edgeSet).Reachable x z := by
      rw [SimpleGraph.fromEdgeSet_edgeSet]; exact hS.preconnected x z
    have := mem_of_reachable_of_closed hclosed (by simp) hr
    simpa using this
  calc Fintype.card K = #(univ : Finset K) := card_univ.symm
    _ ≤ #({x, y} : Finset K) := card_le_card fun z _ => hall z
    _ ≤ 2 := card_le_two
end ChromaticReconstruction

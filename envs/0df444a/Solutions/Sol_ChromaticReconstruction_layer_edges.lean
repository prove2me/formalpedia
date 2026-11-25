-- Prove2me | solution 1 for ChromaticReconstruction.layer_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:16:08.678808+00:00
-- url     : https://prove2.me/submissions/30b9f627-2887-493e-8ca7-70ae352c89f2

import Definitions.Def_RequestProject_Recovery
import Definitions.Def_RequestProject_RecoveryThm
import Theorems.Thm_ChromaticReconstruction_layer_tree
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_masterTerm_edge
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
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
namespace ChromaticReconstruction
theorem _root_.solution (hS : S.IsTree) (hm : ∀ i, 1 ≤ m i) (hk : 2 ≤ Fintype.card K) :
    homogeneousComponent (Fintype.card K - 1) (phi (leafExt S m)) =
      (-1) ^ ((∑ i, m i) - 1 + 1) *
        ((edgeTypes S (fun i => m i + 1)).map (theta (weightMS m))).sum := by
  rw [layer_tree S m hS hm]
  have hfilt : S.edgeFinset.powerset.filter
      (fun F : Finset (Sym2 K) => Fintype.card K = Fintype.card K - 1 + F.card) =
        S.edgeFinset.powersetCard 1 := by
    ext F
    simp only [mem_filter, mem_powerset, mem_powersetCard]
    constructor
    · rintro ⟨hF, h⟩; exact ⟨hF, by omega⟩
    · rintro ⟨hF, h⟩; exact ⟨hF, by omega⟩
  rw [hfilt, powersetCard_one, sum_map]
  unfold edgeTypes
  rw [Multiset.map_map, ← sum_eq_multiset_sum, mul_sum]
  refine sum_congr rfl fun e he => ?_
  simp only [Function.Embedding.coeFn_mk, card_singleton, Function.comp_apply]
  rw [masterTerm_edge S m hm he]
end ChromaticReconstruction

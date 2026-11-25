-- Prove2me | solution 1 for ChromaticReconstruction.layer_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:16:01.563109+00:00
-- url     : https://prove2.me/submissions/614354f7-20a9-47e2-9478-e72112b0a44f

import Definitions.Def_RequestProject_Recovery
import Definitions.Def_RequestProject_RecoveryThm
import Theorems.Thm_ChromaticReconstruction_layer_tree
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_masterTerm_empty
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
theorem _root_.solution (hS : S.IsTree) (hm : ∀ i, 1 ≤ m i) :
    homogeneousComponent (Fintype.card K) (phi (leafExt S m)) =
      (-1) ^ ((∑ i, m i) - 1) * fP (weightMS m) := by
  rw [layer_tree S m hS hm]
  have hfilt : S.edgeFinset.powerset.filter
      (fun F : Finset (Sym2 K) => Fintype.card K = Fintype.card K + F.card) = {∅} := by
    ext F
    simp only [mem_filter, mem_powerset, mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact card_eq_zero.1 (by omega)
    · rintro rfl
      exact ⟨empty_subset _, by simp⟩
  rw [hfilt, sum_singleton, masterTerm_empty m hm, card_empty, add_zero]
end ChromaticReconstruction

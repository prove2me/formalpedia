-- Prove2me | solution 1 for ChromaticReconstruction.masterTerm_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:05:57.155596+00:00
-- url     : https://prove2.me/submissions/7b989e71-d6b7-4338-bc23-698efe1e901d

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_compSets_empty
import Theorems.Thm_ChromaticReconstruction_sum_killP1_eq_fP
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
variable {K : Type*} [Fintype K]
variable (S : SimpleGraph K) (m : K → ℕ)
namespace ChromaticReconstruction
theorem _root_.solution (hm : ∀ i, 1 ≤ m i) : masterTerm m ∅ = fP (weightMS m) := by
  unfold masterTerm weightMS
  rw [coe_empty, compSets_empty, ← sum_killP1_eq_fP univ m (fun i _ => hm i)]
  refine sum_congr rfl fun i _ => ?_
  rw [prod_image (fun a _ b _ h => singleton_injective h)]
  simp only [sum_singleton, mem_singleton]
end ChromaticReconstruction

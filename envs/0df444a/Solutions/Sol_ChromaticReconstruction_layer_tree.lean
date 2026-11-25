-- Prove2me | solution 1 for ChromaticReconstruction.layer_tree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:42.895357+00:00
-- url     : https://prove2.me/submissions/9e1386be-7d20-462d-bb7f-798b576ca560

import Definitions.Def_RequestProject_Recovery
import Definitions.Def_RequestProject_RecoveryThm
import Theorems.Thm_ChromaticReconstruction_card_compSets_add_card_of_isTree
import Theorems.Thm_ChromaticReconstruction_homogeneousComponent_phi_leafExt
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
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
namespace ChromaticReconstruction
theorem _root_.solution (hS : S.IsTree) (hm : ∀ i, 1 ≤ m i) (j : ℕ) :
    homogeneousComponent j (phi (leafExt S m)) =
      ∑ F ∈ S.edgeFinset.powerset.filter
          (fun F : Finset (Sym2 K) => Fintype.card K = j + F.card),
        (-1) ^ ((∑ i, m i) - 1 + F.card) * masterTerm m F := by
  rw [homogeneousComponent_phi_leafExt S m hm]
  apply sum_congr _ (fun _ _ => rfl)
  ext F
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨hF, h⟩
    refine ⟨hF, ?_⟩
    rw [← card_compSets_add_card_of_isTree hS hF, h]
  · rintro ⟨hF, h⟩
    refine ⟨hF, ?_⟩
    have := card_compSets_add_card_of_isTree hS hF
    omega
end ChromaticReconstruction

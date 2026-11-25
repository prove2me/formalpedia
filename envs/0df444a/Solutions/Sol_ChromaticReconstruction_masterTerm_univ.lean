-- Prove2me | solution 1 for ChromaticReconstruction.masterTerm_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:55:14.020751+00:00
-- url     : https://prove2.me/submissions/d08d950d-4cfa-422c-90ed-af29d3296474

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_compSets_edgeSet_of_connected
import Theorems.Thm_ChromaticReconstruction_killP1_X_of_ne
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
theorem _root_.solution (hS : S.Connected) (hn : Fintype.card K + ∑ i, m i ≠ 2) :
    masterTerm m S.edgeFinset =
      ((∑ i, m i : ℕ) : MvPolynomial ℕ ℚ) * X (Fintype.card K + ∑ i, m i - 1) := by
  unfold masterTerm
  rw [SimpleGraph.coe_edgeFinset, compSets_edgeSet_of_connected hS]
  simp only [prod_singleton, mem_univ, if_true]
  have hsum : ∑ j, (m j + 1) = Fintype.card K + ∑ i, m i := by
    rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one, add_comm]
  rw [hsum, killP1_X_of_ne (by omega), ← sum_mul, Nat.cast_sum]
end ChromaticReconstruction

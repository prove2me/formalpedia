-- Prove2me | solution 1 for ChromaticReconstruction.pairMS_le_weightMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:52:33.886796+00:00
-- url     : https://prove2.me/submissions/64c8b801-aeff-49b6-a3a5-977ff7c00f36

import Definitions.Def_RequestProject_Recovery
import Definitions.Def_RequestProject_RecoveryThm
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
theorem _root_.solution {e : Sym2 K} (he : e ∈ S.edgeFinset) :
    pairMS (e.map fun i => m i + 1) ≤ weightMS m := by
  induction e using Sym2.ind with
  | _ u v =>
  have huv : u ≠ v := S.ne_of_adj (by simpa using he)
  rw [Sym2.map_pair_eq, pairMS_mk]
  have : ({m u + 1, m v + 1} : Multiset ℕ) = ({u, v} : Finset K).val.map fun i => m i + 1 := by
    rw [insert_val_of_notMem (by simpa using huv)]
    simp
  rw [this]
  exact Multiset.map_le_map (val_le_iff.2 (subset_univ _))
end ChromaticReconstruction

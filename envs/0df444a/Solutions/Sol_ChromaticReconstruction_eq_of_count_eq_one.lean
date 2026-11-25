-- Prove2me | solution 1 for ChromaticReconstruction.eq_of_count_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:54:18.367775+00:00
-- url     : https://prove2.me/submissions/3bf976f9-7c05-44c6-b98e-909127089d17

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_card_filter_weight
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
variable {K : Type*} [Fintype K]
namespace ChromaticReconstruction
theorem _root_.solution {w : K → ℕ} {a : ℕ} (h : Multiset.count a (wts w) = 1) {x y : K}
    (hx : w x = a) (hy : w y = a) : x = y := by
  rw [← card_filter_weight, card_eq_one] at h
  obtain ⟨z, hz⟩ := h
  have hx' : x ∈ ({z} : Finset K) := hz ▸ (by simp [hx])
  have hy' : y ∈ ({z} : Finset K) := hz ▸ (by simp [hy])
  rw [mem_singleton] at hx' hy'
  rw [hx', hy']
end ChromaticReconstruction

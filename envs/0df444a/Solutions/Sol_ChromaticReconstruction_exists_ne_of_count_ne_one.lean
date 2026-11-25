-- Prove2me | solution 1 for ChromaticReconstruction.exists_ne_of_count_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:58:46.175801+00:00
-- url     : https://prove2.me/submissions/58f34f19-2778-4c33-99e6-5e1acd021b9a

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
theorem _root_.solution {w : K → ℕ} {x : K} (h : Multiset.count (w x) (wts w) ≠ 1) :
    ∃ y, y ≠ x ∧ w y = w x := by
  have hpos : x ∈ (univ.filter fun y => w y = w x) := by simp
  have h2 : 1 < #{y | w y = w x} := by
    rw [card_filter_weight]
    have : 0 < Multiset.count (w x) (wts w) := by
      rw [← card_filter_weight]; exact card_pos.2 ⟨x, hpos⟩
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 h2
  simp only [mem_filter, mem_univ, true_and] at ha hb
  by_cases hax : a = x
  · exact ⟨b, fun h => hab (hax.trans h.symm), hb⟩
  · exact ⟨a, hax, ha⟩
end ChromaticReconstruction

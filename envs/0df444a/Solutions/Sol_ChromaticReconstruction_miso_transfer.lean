-- Prove2me | solution 1 for ChromaticReconstruction.miso_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:44:31.542608+00:00
-- url     : https://prove2.me/submissions/99fc02e4-f21c-4960-bb5d-ef210fd8a204

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_sum_degree_weight
import Theorems.Thm_ChromaticReconstruction_card_filter_weight
import Theorems.Thm_ChromaticReconstruction_degree_pos_of_connected
import Theorems.Thm_ChromaticReconstruction_degree_one_of_repeated
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
variable {K K' : Type*} [Fintype K] [Fintype K'] {S : SimpleGraph K} {S' : SimpleGraph K'}
  {w : K → ℕ} {w' : K' → ℕ}
namespace ChromaticReconstruction
theorem _root_.solution (hS' : S'.Connected) (hk' : 2 ≤ Fintype.card K') (hW : wts w = wts w')
    (hE : edgeTypes S w = edgeTypes S' w') (hMI : MIso S w) : MIso S' w' := by
  intro u v huv hw
  have hall : ∀ x ∈ univ.filter (fun x => w' x = w' u), S'.degree x = 1 := by
    have hrep : Multiset.count (w' u) (wts w) ≠ 1 := by
      rw [hW, ← card_filter_weight]
      have : 1 < #{x | w' x = w' u} := one_lt_card.2 ⟨u, by simp, v, by simp [hw], huv⟩
      omega
    have hsum : ∑ x ∈ univ.filter (fun x => w' x = w' u), 1 =
        ∑ x ∈ univ.filter (fun x => w' x = w' u), S'.degree x := by
      rw [sum_degree_weight S' w' (w' u), ← hE, ← sum_degree_weight S w (w' u),
        sum_congr rfl (fun x hx => degree_one_of_repeated hMI
          (by rw [(mem_filter.1 hx).2]; exact hrep))]
      simp only [sum_const, smul_eq_mul, mul_one]
      rw [card_filter_weight, card_filter_weight, hW]
    intro x hx
    exact ((sum_eq_sum_iff_of_le (fun x _ => degree_pos_of_connected hS' hk' x)).1 hsum x hx).symm
  exact ⟨hall u (by simp), hall v (by simp [hw])⟩
end ChromaticReconstruction

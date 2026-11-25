-- Prove2me | solution 1 for ChromaticReconstruction.three_le_degree_PL_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:53:47.425561+00:00
-- url     : https://prove2.me/submissions/41a786cb-0c0c-45bd-ba8f-7c5ce9c93f75

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
import Theorems.Thm_ChromaticReconstruction_PL_adj_vx
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_vx_inj
import Theorems.Thm_ChromaticReconstruction_vx_val
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.vx_val



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n : ℕ} (hn : 3 ≤ n) : 3 ≤ (PL n 1).degree (vx n 1) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : ({vx n 0, vx n 2, vx n n} : Finset _) ⊆ (PL n 1).neighborFinset (vx n 1) := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rw [SimpleGraph.mem_neighborFinset]
    rcases hy with rfl | rfl | rfl <;> rw [PL_adj_vx (by omega) (by omega)] <;> omega
  have h3 : ({vx n 0, vx n 2, vx n n} : Finset _).card = 3 := by
    rw [card_insert_of_notMem, card_pair]
    · rw [Ne, vx_inj (by omega) le_rfl]; omega
    · simp only [mem_insert, mem_singleton, vx_inj (by omega : 0 ≤ n) (by omega : 2 ≤ n),
        vx_inj (by omega : 0 ≤ n) le_rfl]
      omega
  have := card_le_card hsub
  omega
end ChromaticReconstruction

-- Prove2me | solution 1 for ChromaticReconstruction.degree_le_two_PL_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:22:06.994141+00:00
-- url     : https://prove2.me/submissions/63a822ac-ac26-4fd1-9221-7b340a65210a

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
import Theorems.Thm_ChromaticReconstruction_degree_le_of_adj
import Theorems.Thm_ChromaticReconstruction_PL_adj_vx
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_vx_eq_self
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
theorem _root_.solution {n : ℕ} (x : Fin (n + 1)) : (PL n 0).degree x ≤ 2 := by
  have hx := x.isLt
  refine (degree_le_of_adj {vx n (if x.val = 0 then n else if x.val = n then 0 else x.val - 1),
    vx n (x.val + 1)} fun y hy => ?_).trans (card_le_two)
  have hy' := y.isLt
  rw [← vx_eq_self x, ← vx_eq_self y, PL_adj_vx (by omega) (by omega)] at hy
  rw [mem_insert, mem_singleton, ← vx_eq_self y, Fin.ext_iff, Fin.ext_iff]
  simp only [vx_val]
  split_ifs <;> omega
end ChromaticReconstruction

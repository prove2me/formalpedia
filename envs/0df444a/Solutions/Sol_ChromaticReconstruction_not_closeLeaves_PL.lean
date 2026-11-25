-- Prove2me | solution 1 for ChromaticReconstruction.not_closeLeaves_PL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:05.54593+00:00
-- url     : https://prove2.me/submissions/d94b1c05-ef96-4983-b60a-101ec1d6e8f3

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
import Theorems.Thm_ChromaticReconstruction_walk_potential
import Theorems.Thm_ChromaticReconstruction_leaf_val_PL
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
theorem _root_.solution {n b : ℕ} (hb : 1 ≤ b) (hn : 2 * b + 1 ≤ n) :
    ¬ CloseLeaves (PL n b) b := by
  rintro ⟨u, v, huv, hu, hv, w, hw⟩
  have hfa : ∀ x y, (PL n b).Adj x y →
      (fun z : Fin (n + 1) => if z.val = n then b + 1 else z.val) y ≤
        (fun z : Fin (n + 1) => if z.val = n then b + 1 else z.val) x + 1 := by
    intro x y h
    rw [← vx_eq_self x, ← vx_eq_self y, PL_adj_vx (by omega) (by omega)] at h
    have := x.isLt; have := y.isLt
    simp only; split_ifs <;> omega
  have hga : ∀ x y, (PL n b).Adj x y →
      (fun z : Fin (n + 1) => if z.val = n then n - b else n - 1 - z.val) y ≤
        (fun z : Fin (n + 1) => if z.val = n then n - b else n - 1 - z.val) x + 1 := by
    intro x y h
    rw [← vx_eq_self x, ← vx_eq_self y, PL_adj_vx (by omega) (by omega)] at h
    have := x.isLt; have := y.isLt
    simp only; split_ifs <;> omega
  have h1 := walk_potential _ hfa w
  have h2 := walk_potential _ hfa w.reverse
  have h3 := walk_potential _ hga w
  have h4 := walk_potential _ hga w.reverse
  rw [SimpleGraph.Walk.length_reverse] at h2 h4
  have hu' := leaf_val_PL u hu
  have hv' := leaf_val_PL v hv
  have huv' : u.val ≠ v.val := fun h => huv (Fin.ext h)
  split_ifs at h1 h2 h3 h4 <;> omega
end ChromaticReconstruction

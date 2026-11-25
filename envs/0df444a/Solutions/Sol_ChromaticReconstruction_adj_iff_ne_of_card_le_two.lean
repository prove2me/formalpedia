-- Prove2me | solution 1 for ChromaticReconstruction.adj_iff_ne_of_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:01:18.727162+00:00
-- url     : https://prove2.me/submissions/84263308-01b3-4770-8386-a1ba5f80443d

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
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
variable {K : Type*} [Fintype K] {S : SimpleGraph K}
namespace ChromaticReconstruction
theorem _root_.solution (hS : S.Connected) (hk : Fintype.card K ≤ 2) {x y : K} :
    S.Adj x y ↔ x ≠ y := by
  refine ⟨S.ne_of_adj, fun hxy => ?_⟩
  obtain ⟨p⟩ := hS.preconnected x y
  cases p with
  | nil => exact absurd rfl hxy
  | @cons _ z _ h p =>
    by_cases hzy : z = y
    · rwa [← hzy]
    · exfalso
      have hxz : x ≠ z := S.ne_of_adj h
      have : #({x, y, z} : Finset K) = 3 := by
        rw [card_insert_of_notMem (by simp [hxy, hxz]), card_pair (Ne.symm hzy)]
      have := card_le_univ ({x, y, z} : Finset K)
      omega
end ChromaticReconstruction

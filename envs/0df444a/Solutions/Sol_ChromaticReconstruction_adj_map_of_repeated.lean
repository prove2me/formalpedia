-- Prove2me | solution 1 for ChromaticReconstruction.adj_map_of_repeated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:53:43.16324+00:00
-- url     : https://prove2.me/submissions/499ab8b1-9df9-46b1-8502-fdd9623c6f05

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_eq_of_count_eq_one
import Theorems.Thm_ChromaticReconstruction_neighborFinset_eq_of_degree_one
import Theorems.Thm_ChromaticReconstruction_degree_one_of_repeated
import Theorems.Thm_ChromaticReconstruction_unique_of_adj_leaf
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
theorem _root_.solution (hS : S.Connected) (hk : 3 ≤ Fintype.card K) (hMI : MIso S w)
    (hW : wts w = wts w') (φ : K ≃ K') (hkey : ∀ x, keyOf S' w' (φ x) = keyOf S w x) {x y : K}
    (hxy : S.Adj x y) (hx : Multiset.count (w x) (wts w) ≠ 1) : S'.Adj (φ x) (φ y) := by
  have hw : ∀ x, w' (φ x) = w x := fun x => congrArg Prod.fst (hkey x)
  have hdeg := degree_one_of_repeated hMI hx
  have hnb := neighborFinset_eq_of_degree_one hdeg hxy
  have h2 : (S'.neighborFinset (φ x)).val.map w' = {w y} := by
    have := congrArg Prod.snd (hkey x)
    simp only [keyOf] at this
    rw [hw x, ← hW, if_neg hx, if_neg hx, hnb] at this
    simpa using this
  have hmem : w y ∈ (S'.neighborFinset (φ x)).val.map w' := by rw [h2]; simp
  obtain ⟨z, hz, hzw⟩ := Multiset.mem_map.1 hmem
  have hyu := unique_of_adj_leaf hS hk hMI hdeg hxy
  rw [hW] at hyu
  have : z = φ y := eq_of_count_eq_one hyu hzw (hw y)
  rw [← this]
  exact (S'.mem_neighborFinset _ _).1 hz
end ChromaticReconstruction

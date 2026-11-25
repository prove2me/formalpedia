-- Prove2me | solution 1 for ChromaticReconstruction.sum_card_nbr_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:58:32.540352+00:00
-- url     : https://prove2.me/submissions/baf02bd6-3cc5-4d6d-ab5a-28393c2a5172

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_sum_card_nbr_filter
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
variable {K : Type*} [Fintype K] (S : SimpleGraph K)
variable (w : K → ℕ)
namespace ChromaticReconstruction
theorem _root_.solution {a b : ℕ} (hab : a ≠ b) :
    ∑ x ∈ univ.filter (fun x => w x = a), #{y ∈ S.neighborFinset x | w y = b} =
      Multiset.count s(a, b) (edgeTypes S w) := by
  have h := sum_card_nbr_filter S (fun x y => w x = a ∧ w y = b)
  rw [sum_filter]
  have e1 : ∀ x, #{y ∈ S.neighborFinset x | w x = a ∧ w y = b} =
      if w x = a then #{y ∈ S.neighborFinset x | w y = b} else 0 := by
    intro x
    split_ifs with hx
    · simp [hx]
    · simp [hx]
  simp only [e1] at h
  rw [h, edgeTypes, Multiset.count_map, ← filter_val, ← card_def, card_filter]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ x y =>
  simp only [pairCount, Sym2.lift_mk, Sym2.map_pair_eq, Sym2.eq_iff]
  by_cases h1 : w x = a <;> by_cases h2 : w y = b <;> by_cases h3 : w y = a <;>
    by_cases h4 : w x = b <;> simp_all <;> omega
end ChromaticReconstruction

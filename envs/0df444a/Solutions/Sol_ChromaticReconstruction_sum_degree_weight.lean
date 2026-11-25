-- Prove2me | solution 1 for ChromaticReconstruction.sum_degree_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:55:37.632586+00:00
-- url     : https://prove2.me/submissions/bff7f63f-b04a-4ec5-8208-54f382148509

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
theorem _root_.solution (a : ℕ) :
    ∑ x ∈ univ.filter (fun x => w x = a), S.degree x =
      ((edgeTypes S w).map fun z => Multiset.count a (pairMS z)).sum := by
  have h := sum_card_nbr_filter S (fun x _ => w x = a)
  rw [sum_filter]
  have e1 : ∀ x, #{y ∈ S.neighborFinset x | w x = a} = if w x = a then S.degree x else 0 := by
    intro x
    split_ifs with hx
    · rw [filter_true_of_mem (fun _ _ => hx), SimpleGraph.card_neighborFinset_eq_degree]
    · rw [filter_false_of_mem (fun _ _ => hx), card_empty]
  simp only [e1] at h
  rw [h, edgeTypes, Multiset.map_map, ← sum_eq_multiset_sum]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ x y =>
  simp only [pairCount, Sym2.lift_mk, Function.comp_apply, Sym2.map_pair_eq, pairMS_mk,
    Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, @eq_comm ℕ a]
  omega
end ChromaticReconstruction

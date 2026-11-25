-- Prove2me | solution 1 for ChromaticReconstruction.sum_card_nbr_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:54:05.451068+00:00
-- url     : https://prove2.me/submissions/e4549584-b429-46a0-b56f-1a8f3db2bc09

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
variable {K : Type*} [Fintype K] (S : SimpleGraph K)
namespace ChromaticReconstruction
theorem _root_.solution (Q : K → K → Prop) [DecidableRel Q] :
    ∑ x, #{y ∈ S.neighborFinset x | Q x y} = ∑ e ∈ S.edgeFinset, pairCount Q e := by
  have hA : ∀ x, #{y ∈ S.neighborFinset x | Q x y} =
      #{d ∈ (univ.filter fun d : S.Dart => Q d.fst d.snd) | d.fst = x} := by
    intro x
    refine card_bij' (fun y hy => (⟨(x, y), (S.mem_neighborFinset x y).1
        (mem_filter.1 hy).1⟩ : S.Dart)) (fun d _ => d.snd) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      simpa using hy.2
    · intro d hd
      simp only [mem_filter, mem_univ, true_and] at hd ⊢
      obtain ⟨hQ, rfl⟩ := hd
      exact ⟨(S.mem_neighborFinset _ _).2 d.adj, hQ⟩
    · intro y hy; rfl
    · intro d hd
      simp only [mem_filter, mem_univ, true_and] at hd
      obtain ⟨-, rfl⟩ := hd
      rfl
  rw [sum_congr rfl fun x _ => hA x, ← card_eq_sum_card_fiberwise
      (f := fun d : S.Dart => d.fst) (t := univ) (fun d _ => mem_univ _),
    card_eq_sum_card_fiberwise (f := fun d : S.Dart => d.edge) (t := S.edgeFinset)
      (fun d _ => by simp)]
  refine sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ x y =>
  have hxy : S.Adj x y := by simpa using he
  let d0 : S.Dart := ⟨(x, y), hxy⟩
  have hfib : (univ.filter fun d : S.Dart => Q d.fst d.snd ∧ d.edge = s(x, y)) =
      ({d0, d0.symm} : Finset S.Dart).filter (fun d => Q d.fst d.snd) := by
    ext d
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    rw [← SimpleGraph.dart_edge_eq_iff d d0]
    exact and_comm
  rw [filter_filter, hfib, card_filter, sum_pair (d0.symm_ne).symm]
  rfl
end ChromaticReconstruction

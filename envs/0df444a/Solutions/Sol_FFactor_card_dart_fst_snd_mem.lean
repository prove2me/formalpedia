-- Prove2me | solution 1 for FFactor.card_dart_fst_snd_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:03:56.216299+00:00
-- url     : https://prove2.me/submissions/31acdca1-c583-4ad0-9942-84deb44c456e

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
public import Theorems.Thm_FFactor_gadget_adj_inl_inl
public import Theorems.Thm_FFactor_gadget_adj_inl_inr
public import Theorems.Thm_FFactor_gadget_adj_inr_inl
public import Theorems.Thm_FFactor_gadget_adj_inr_inr
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_mem_del_verts
attribute [local simp] FFactor.gadget_adj_inl_inl
attribute [local simp] FFactor.gadget_adj_inl_inr
attribute [local simp] FFactor.gadget_adj_inr_inl
attribute [local simp] FFactor.gadget_adj_inr_inr
attribute [local simp] FFactor.home_inl
attribute [local simp] FFactor.home_inr
attribute [local simp] FFactor.mem_del_verts



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution (T S : Finset V) :
    #{d : G.Dart | d.fst ∈ T ∧ d.snd ∈ S} = ∑ t ∈ T, #{u | G.Adj t u ∧ u ∈ S} := by
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.fst) (t := T)
    (fun d hd => (mem_filter.mp hd).2.1)]
  refine sum_congr rfl (fun t ht => ?_)
  apply card_bij (fun d _ => d.snd)
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    exact ⟨hd.2 ▸ d.adj, hd.1.2⟩
  · intro d hd d' hd' h
    simp only [mem_filter, mem_univ, true_and] at hd hd'
    exact Dart.ext _ _ (Prod.ext (hd.2.trans hd'.2.symm) h)
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    exact ⟨⟨(t, u), hu.1⟩, by simp [ht, hu.2], rfl⟩
end FFactor

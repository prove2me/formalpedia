-- Prove2me | solution 1 for FFactor.card_dart_snd_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:03:23.102281+00:00
-- url     : https://prove2.me/submissions/949db98e-c91f-4171-87ec-6c6de2145171

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
theorem _root_.solution (r : V) (T : Finset V) :
    #{d : G.Dart | d.fst ∈ T ∧ d.snd = r} = #{t ∈ T | G.Adj r t} := by
  apply card_bij (fun d _ => d.fst)
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    exact ⟨hd.1, hd.2 ▸ d.adj.symm⟩
  · intro d _ d' _ h
    simp only [mem_filter, mem_univ, true_and] at *
    exact Dart.ext _ _ (Prod.ext h (by simp_all))
  · intro t ht
    simp only [mem_filter] at ht
    exact ⟨⟨(t, r), ht.2.symm⟩, by simp [ht.1], rfl⟩
end FFactor

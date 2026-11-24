-- Prove2me | solution 1 for FFactor.reach_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:06:07.061604+00:00
-- url     : https://prove2.me/submissions/24883f78-81e7-4760-94ce-221bce9b00c2

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_F3
public import Theorems.Thm_FFactor_exists_dart_of_notMem_Tset
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_reach_adj
public import Theorems.Thm_FFactor_notMem_S_of_notMem_union
public import Theorems.Thm_FFactor_gadget_adj_inl_inl
public import Theorems.Thm_FFactor_gadget_adj_inl_inr
public import Theorems.Thm_FFactor_gadget_adj_inr_inl
public import Theorems.Thm_FFactor_gadget_adj_inr_inr
public import Theorems.Thm_FFactor_mem_del_verts
attribute [local simp] FFactor.gadget_adj_inl_inl
attribute [local simp] FFactor.gadget_adj_inl_inr
attribute [local simp] FFactor.gadget_adj_inr_inl
attribute [local simp] FFactor.gadget_adj_inr_inr
attribute [local simp] FFactor.mem_del_verts


attribute [local simp] FFactor.home_inl
attribute [local simp] FFactor.home_inr

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable [DecidableEq V] {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {r : V}
    (hr : r ∉ Sset G f U ∪ Tset G f U) (x : GV G f) (hx : x ∉ U)
    (hxr : home G f U x = r) (i : Fin (G.degree r - f r)) :
    (del (gadget G f) U).Reachable ⟨x, (mem_del_verts _).mpr hx⟩
      ⟨.inr ⟨r, i⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union hr) i)⟩ := by
  have hrT := notMem_T_of_notMem_union hr
  have hrS := notMem_S_of_notMem_union hr
  rcases x with d | ⟨r', j⟩
  · simp only [home_inl] at hxr
    by_cases ht : d.fst ∈ Tset G f U
    · rw [if_pos ht] at hxr
      have hs : (.inl d.symm : GV G f) ∉ U := F3 hmin hrT hrS (d := d.symm) hxr
      exact (reach_adj hx hs rfl).trans (reach_adj hs (F1 hmin hrT i) hxr)
    · rw [if_neg ht] at hxr
      exact reach_adj hx (F1 hmin hrT i) hxr
  · simp only [home_inr] at hxr
    subst hxr
    obtain ⟨z, hz⟩ := exists_dart_of_notMem_Tset hrT
    have hzU : (.inl z : GV G f) ∉ U := F3 hmin hrT hrS hz
    exact (reach_adj hx hzU hz).trans (reach_adj hzU (F1 hmin hrT i) hz)
end FFactor

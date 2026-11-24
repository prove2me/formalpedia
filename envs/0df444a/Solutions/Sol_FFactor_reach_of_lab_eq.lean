-- Prove2me | solution 1 for FFactor.reach_of_lab_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:11:14.861021+00:00
-- url     : https://prove2.me/submissions/8fae82d7-b042-4ff0-86b2-cb5435f7eef2

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_exists_inner_of_notMem_Tset
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_lab_of_notMem
public import Theorems.Thm_FFactor_lab_inl_of_mem
public import Theorems.Thm_FFactor_lab_inr_of_mem
public import Theorems.Thm_FFactor_reach_adj
public import Theorems.Thm_FFactor_reach_inner
public import Theorems.Thm_FFactor_reach_inner_of_reachable
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
theorem _root_.solution (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) (a b : GV G f)
    (ha : a ∉ U) (hb : b ∉ U) (hab : lab G f U a = lab G f U b) :
    (del (gadget G f) U).Reachable ⟨a, (mem_del_verts _).mpr ha⟩
      ⟨b, (mem_del_verts _).mpr hb⟩ := by
  by_cases hha : home G f U a ∈ Sset G f U ∪ Tset G f U
  · rcases a with d | p <;> rcases b with d' | q
    · by_cases hhb : home G f U (.inl d') ∈ Sset G f U ∪ Tset G f U
      · rw [lab_inl_of_mem hha, lab_inl_of_mem hhb] at hab
        simp only [Sum.inr.injEq, Sum.inl.injEq] at hab
        rcases (dart_edge_eq_iff _ _).mp hab with h | h
        · subst h; rfl
        · subst h
          exact reach_adj ha hb (by simp)
      · rw [lab_inl_of_mem hha, lab_of_notMem hhb] at hab
        simp at hab
    · by_cases hhb : home G f U (.inr q) ∈ Sset G f U ∪ Tset G f U
      · rw [lab_inl_of_mem hha, lab_inr_of_mem hhb] at hab
        simp at hab
      · rw [lab_inl_of_mem hha, lab_of_notMem hhb] at hab
        simp at hab
    · by_cases hhb : home G f U (.inl d') ∈ Sset G f U ∪ Tset G f U
      · rw [lab_inr_of_mem hha, lab_inl_of_mem hhb] at hab
        simp at hab
      · rw [lab_inr_of_mem hha, lab_of_notMem hhb] at hab
        simp at hab
    · by_cases hhb : home G f U (.inr q) ∈ Sset G f U ∪ Tset G f U
      · rw [lab_inr_of_mem hha, lab_inr_of_mem hhb] at hab
        simp only [Sum.inr.injEq] at hab
        subst hab; rfl
      · rw [lab_inr_of_mem hha, lab_of_notMem hhb] at hab
        simp at hab
  · by_cases hhb : home G f U b ∈ Sset G f U ∪ Tset G f U
    · exfalso
      rw [lab_of_notMem hha] at hab
      rcases b with d' | q
      · rw [lab_inl_of_mem hhb] at hab; simp at hab
      · rw [lab_inr_of_mem hhb] at hab; simp at hab
    · rw [lab_of_notMem hha, lab_of_notMem hhb] at hab
      simp only [Sum.inl.injEq] at hab
      obtain ⟨p⟩ := ConnectedComponent.exact hab
      obtain ⟨i, -⟩ := exists_inner_of_notMem_Tset (notMem_T_of_notMem_union hha)
      obtain ⟨i', -⟩ := exists_inner_of_notMem_Tset (notMem_T_of_notMem_union hhb)
      exact (reach_inner hmin hha a ha rfl i).trans
        ((reach_inner_of_reachable hmin p i i').trans (reach_inner hmin hhb b hb rfl i').symm)
end FFactor

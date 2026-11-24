-- Prove2me | solution 1 for FFactor.lab_eq_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:06:58.87148+00:00
-- url     : https://prove2.me/submissions/893d1c6a-d73e-4e15-a63f-bac91c6efc05

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_lab_of_notMem
public import Theorems.Thm_FFactor_lab_inl_of_mem
public import Theorems.Thm_FFactor_lab_eq_of_home_eq
public import Theorems.Thm_FFactor_fst_notMem_S_of_notMem
public import Theorems.Thm_FFactor_lab_eq_of_adj_inl_inr
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
theorem _root_.solution (a b : GV G f) (ha : a ∉ U) (hb : b ∉ U) (hadj : (gadget G f).Adj a b) :
    lab G f U a = lab G f U b := by
  rcases a with d | p <;> rcases b with d' | p'
  · simp only [gadget_adj_inl_inl] at hadj
    subst hadj
    have hS1 := fst_notMem_S_of_notMem ha
    have hS2 : d.snd ∉ Sset G f U := fst_notMem_S_of_notMem (d := d.symm) hb
    by_cases ht1 : d.fst ∈ Tset G f U <;> by_cases ht2 : d.snd ∈ Tset G f U
    · rw [lab_inl_of_mem (by simp [ht1, ht2]), lab_inl_of_mem (by simp [ht1, ht2]),
        Dart.edge_symm]
    · apply lab_eq_of_home_eq
      · simp [ht1, ht2]
      · simp [ht1, ht2, hS2]
    · apply lab_eq_of_home_eq
      · simp [ht1, ht2]
      · simp [ht1, hS1]
    · rw [lab_of_notMem (by simp [ht1, hS1]), lab_of_notMem (by simp [ht2, hS2])]
      congr 1
      apply ConnectedComponent.connectedComponentMk_eq_of_adj
      simp [ht1, ht2, d.adj]
  · exact lab_eq_of_adj_inl_inr ha hb hadj
  · exact (lab_eq_of_adj_inl_inr hb ha hadj).symm
  · exact absurd hadj (gadget_adj_inr_inr _ _)
end FFactor

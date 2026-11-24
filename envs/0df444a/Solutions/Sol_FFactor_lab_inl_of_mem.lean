-- Prove2me | solution 1 for FFactor.lab_inl_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:58:39.346739+00:00
-- url     : https://prove2.me/submissions/6adcf3eb-b27f-4a1b-b995-361055e31f6a

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
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
theorem _root_.solution {d : G.Dart} (h : home G f U (.inl d) ∈ Sset G f U ∪ Tset G f U) :
    lab G f U (.inl d) = .inr (.inl d.edge) := by
  simp only [lab, h, not_true_eq_false, dite_false]
end FFactor

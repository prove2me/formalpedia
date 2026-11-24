-- Prove2me | solution 1 for FFactor.mem_Sset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:59:06.610805+00:00
-- url     : https://prove2.me/submissions/31da29a4-c1b9-4a42-a650-16623d2fdac6

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
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



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution {v : V} : v ∈ Sset G f U ↔
    v ∉ Tset G f U ∧ ∀ d : G.Dart, d.fst = v → (.inl d : GV G f) ∈ U := by
  simp [Sset]
end FFactor

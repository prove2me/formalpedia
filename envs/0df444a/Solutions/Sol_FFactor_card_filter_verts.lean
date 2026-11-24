-- Prove2me | solution 1 for FFactor.card_filter_verts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:00:32.155318+00:00
-- url     : https://prove2.me/submissions/7c10d90b-0c17-4c09-9617-914d3baa912d

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
omit [DecidableEq V]
namespace FFactor
theorem _root_.solution (P : GV G f → Prop) [DecidablePred P]
    [DecidablePred (fun x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts => P x.1)] :
    #{x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts | P x.1} = #{a | a ∉ U ∧ P a} := by
  apply card_bij (fun x _ => x.1)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨(mem_del_verts _).mp x.2, hx⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    exact ⟨⟨a, (mem_del_verts _).mpr ha.1⟩, by simpa using ha.2, rfl⟩
end FFactor

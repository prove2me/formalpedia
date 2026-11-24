-- Prove2me | solution 1 for FFactor.reach_inner_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:08:28.404587+00:00
-- url     : https://prove2.me/submissions/07d6e2e2-8ee4-48f6-8cd5-1aad08273279

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_F3
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_reach_adj
public import Theorems.Thm_FFactor_notMem_S_of_notMem_union
public import Theorems.Thm_FFactor_reach_inner
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
theorem _root_.solution (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {r r' : V}
    (hr : r ∉ Sset G f U ∪ Tset G f U) (hr' : r' ∉ Sset G f U ∪ Tset G f U)
    (hadj : G.Adj r r') (i : Fin (G.degree r - f r)) (i' : Fin (G.degree r' - f r')) :
    (del (gadget G f) U).Reachable
      ⟨.inr ⟨r, i⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union hr) i)⟩
      ⟨.inr ⟨r', i'⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union hr') i')⟩ := by
  let d : G.Dart := ⟨(r, r'), hadj⟩
  have hd : (.inl d : GV G f) ∉ U :=
    F3 hmin (notMem_T_of_notMem_union hr) (notMem_S_of_notMem_union hr) (d := d) rfl
  have hd' : (.inl d.symm : GV G f) ∉ U :=
    F3 hmin (notMem_T_of_notMem_union hr') (notMem_S_of_notMem_union hr') (d := d.symm) rfl
  have h1 := reach_inner hmin hr (.inl d) hd
    (by simp [d, notMem_T_of_notMem_union hr]) i
  have h2 := reach_inner hmin hr' (.inl d.symm) hd'
    (by simp [d, notMem_T_of_notMem_union hr']) i'
  exact h1.symm.trans ((reach_adj hd hd' rfl).trans h2)
end FFactor

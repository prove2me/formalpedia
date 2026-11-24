-- Prove2me | solution 1 for FFactor.lab_eq_of_adj_inl_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:04:34.471793+00:00
-- url     : https://prove2.me/submissions/c7b65898-a1b4-4dea-a3f0-d696ae298234

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_lab_eq_of_home_eq
public import Theorems.Thm_FFactor_fst_notMem_S_of_notMem
public import Theorems.Thm_FFactor_notMem_T_of_inner_notMem
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
theorem _root_.solution {d : G.Dart} {p : Σ v : V, Fin (G.degree v - f v)}
    (ha : (.inl d : GV G f) ∉ U) (hb : (.inr p : GV G f) ∉ U) (hadj : d.fst = p.1) :
    lab G f U (.inl d) = lab G f U (.inr p) := by
  obtain ⟨v, i⟩ := p
  simp only at hadj
  subst hadj
  have hT := notMem_T_of_inner_notMem hb
  have hS := fst_notMem_S_of_notMem ha
  apply lab_eq_of_home_eq
  · simp [hT]
  · simp [hT, hS]
end FFactor

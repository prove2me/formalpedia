-- Prove2me | solution 1 for FFactor.card_dart_fst_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:03:54.11597+00:00
-- url     : https://prove2.me/submissions/83ee6205-85fd-4491-bc00-5b0d1520c55d

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
theorem _root_.solution (s0 : Finset V) :
    #{d : G.Dart | d.fst ∈ s0} = ∑ v ∈ s0, G.degree v := by
  rw [card_eq_sum_card_fiberwise (s := {d : G.Dart | d.fst ∈ s0}) (f := fun d : G.Dart => d.fst)
    (t := s0) (fun d hd => (mem_filter.mp hd).2)]
  refine sum_congr rfl (fun v hv => ?_)
  rw [← G.dart_fst_fiber_card_eq_degree v, filter_filter]
  congr 1
  ext d
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hv, h⟩
end FFactor

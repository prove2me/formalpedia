-- Prove2me | solution 1 for FFactor.card_fiber_TT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:06:34.8407+00:00
-- url     : https://prove2.me/submissions/bbbe7e39-da15-4182-9efd-80d36c806e42

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
public import Theorems.Thm_P2M_FFactor_card_filter_congr__c7ce8e64b074
public import Theorems.Thm_FFactor_card_filter_verts
public import Theorems.Thm_FFactor_F2
public import Theorems.Thm_FFactor_gadget_adj_inl_inl
public import Theorems.Thm_FFactor_gadget_adj_inl_inr
public import Theorems.Thm_FFactor_gadget_adj_inr_inl
public import Theorems.Thm_FFactor_gadget_adj_inr_inr
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_lab_inl_of_mem
public import Theorems.Thm_FFactor_lab_inr_of_mem
public import Theorems.Thm_FFactor_lab_of_notMem
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
theorem _root_.solution (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {d : G.Dart}
    (hd : (.inl d : GV G f) ∉ U) (h1 : d.fst ∈ Tset G f U) (h2 : d.snd ∈ Tset G f U) :
    #{x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts |
      lab G f U x.1 = .inr (.inl d.edge)} = 2 := by
  have hmemd : home G f U (.inl d) ∈ Sset G f U ∪ Tset G f U := by
    simp [h1, h2]
  have hds : (.inl d.symm : GV G f) ∉ U := F2 hmin h2 (d := d.symm) rfl
  have hmemds : home G f U (.inl d.symm) ∈ Sset G f U ∪ Tset G f U := by
    simp [h1, h2]
  rw [card_filter_verts (U := U) (fun a => lab G f U a = .inr (.inl d.edge))]
  rw [card_filter_congr' _ (fun a => a ∈ ({.inl d, .inl d.symm} : Finset (GV G f)))]
  · rw [filter_univ_mem, card_pair]
    intro h
    exact d.symm_ne (Sum.inl_injective h).symm
  · intro a
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro ⟨haU, hlab⟩
      rcases a with d' | q
      · by_cases hh : home G f U (.inl d') ∈ Sset G f U ∪ Tset G f U
        · rw [lab_inl_of_mem hh] at hlab
          simp only [Sum.inr.injEq, Sum.inl.injEq] at hlab
          rcases (dart_edge_eq_iff _ _).mp hlab with h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr (by rw [h])
        · rw [lab_of_notMem hh] at hlab; simp at hlab
      · by_cases hh : home G f U (.inr q) ∈ Sset G f U ∪ Tset G f U
        · rw [lab_inr_of_mem hh] at hlab; simp at hlab
        · rw [lab_of_notMem hh] at hlab; simp at hlab
    · rintro (rfl | rfl)
      · exact ⟨hd, lab_inl_of_mem hmemd⟩
      · exact ⟨hds, by rw [lab_inl_of_mem hmemds, Dart.edge_symm]⟩
end FFactor

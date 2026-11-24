-- Prove2me | solution 1 for FFactor.ncard_odd_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:13:38.482831+00:00
-- url     : https://prove2.me/submissions/2b2e7974-9048-4623-9043-f42d0c94c903

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
public import Theorems.Thm_P2M_FFactor_card_filter_congr__c7ce8e64b074
public import Theorems.Thm_FFactor_odd_fiber_iff
public import Theorems.Thm_FFactor_card_fiber_TT
public import Theorems.Thm_FFactor_fst_notMem_S_of_notMem
public import Theorems.Thm_FFactor_gadget_adj_inl_inl
public import Theorems.Thm_FFactor_gadget_adj_inl_inr
public import Theorems.Thm_FFactor_gadget_adj_inr_inl
public import Theorems.Thm_FFactor_gadget_adj_inr_inr
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_lab_eq_of_adj
public import Theorems.Thm_FFactor_lab_inl_of_mem
public import Theorems.Thm_FFactor_lab_inr_of_mem
public import Theorems.Thm_FFactor_lab_of_notMem
public import Theorems.Thm_FFactor_mem_del_verts
public import Theorems.Thm_FFactor_notMem_T_of_inner_notMem
public import Theorems.Thm_FFactor_oddComponents_ncard_eq_of_label
public import Theorems.Thm_FFactor_reach_of_lab_eq
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
theorem _root_.solution (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x)
    (hf : ∀ v, f v ≤ G.degree v) :
    (del (gadget G f) U).oddComponents.ncard ≤ oddCnt G f (Sset G f U) (Tset G f U) +
      #{d : G.Dart | d.fst ∈ Tset G f U ∧ d.snd ∈ Sset G f U} +
      #{p : Σ v : V, Fin (G.degree v - f v) | p.1 ∈ Sset G f U} := by
  let φ : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts →
      (Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f) := fun x => lab G f U x.1
  rw [oddComponents_ncard_eq_of_label (del (gadget G f) U) φ
    (fun x y h => lab_eq_of_adj _ _ ((mem_del_verts _).mp x.2) ((mem_del_verts _).mp y.2)
      ((del_adj _).mp h))
    (fun x y h => reach_of_lab_eq hmin x.1 y.1 ((mem_del_verts _).mp x.2)
      ((mem_del_verts _).mp y.2) h)]
  let A := (univ.filter (fun c : (Gr G f U).ConnectedComponent =>
    Odd #{x | φ x = .inl c})).image
    (fun c => (.inl c : (Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f)))
  let B := (univ.filter (fun d : G.Dart => d.fst ∈ Tset G f U ∧ d.snd ∈ Sset G f U)).image
    (fun d => (.inr (.inl d.edge) : (Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f)))
  let C := (univ.filter (fun p : Σ v : V, Fin (G.degree v - f v) => p.1 ∈ Sset G f U)).image
    (fun p => (.inr (.inr (.inr p)) : (Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f)))
  have hsub : ({l ∈ univ.image φ | Odd #{x | φ x = l}} :
      Finset ((Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f))) ⊆ A ∪ B ∪ C := by
    intro l hl
    simp only [mem_filter, mem_image, mem_univ, true_and] at hl
    obtain ⟨⟨x, rfl⟩, hodd⟩ := hl
    obtain ⟨a, ha⟩ := x
    have haU : a ∉ U := (mem_del_verts _).mp ha
    simp only [mem_union]
    by_cases hh : home G f U a ∈ Sset G f U ∪ Tset G f U
    · rcases a with d | p
      · have hS := fst_notMem_S_of_notMem haU
        have hT : d.fst ∈ Tset G f U := by
          by_contra hT
          rw [home_inl, if_neg hT] at hh
          rcases mem_union.mp hh with h | h
          · exact hS h
          · exact hT h
        have hsnd : d.snd ∈ Sset G f U ∪ Tset G f U := by rwa [home_inl, if_pos hT] at hh
        have hφ : φ ⟨.inl d, ha⟩ = .inr (.inl d.edge) := lab_inl_of_mem hh
        by_cases hsS : d.snd ∈ Sset G f U
        · left; right
          rw [hφ]
          exact mem_image.mpr ⟨d, by simp [hT, hsS], rfl⟩
        · exfalso
          have hsT : d.snd ∈ Tset G f U := by
            rcases mem_union.mp hsnd with h | h
            · exact absurd h hsS
            · exact h
          rw [hφ] at hodd
          have := card_fiber_TT hmin haU hT hsT
          rw [this] at hodd
          exact (Nat.not_odd_iff_even.mpr even_two) hodd
      · right
        have hφ : φ ⟨.inr p, ha⟩ = .inr (.inr (.inr p)) := lab_inr_of_mem hh
        rw [hφ]
        have hpT : p.1 ∉ Tset G f U := by
          obtain ⟨v, i⟩ := p
          exact notMem_T_of_inner_notMem haU
        have hpS : p.1 ∈ Sset G f U := by
          rcases mem_union.mp hh with h | h
          · exact h
          · exact absurd h hpT
        exact mem_image.mpr ⟨p, by simp [hpS], rfl⟩
    · left; left
      have hφ : φ ⟨a, ha⟩ = .inl ((Gr G f U).connectedComponentMk ⟨home G f U a, hh⟩) :=
        lab_of_notMem hh
      rw [hφ] at hodd ⊢
      exact mem_image.mpr ⟨_, by simpa using hodd, rfl⟩
  have hA : #A ≤ oddCnt G f (Sset G f U) (Tset G f U) := by
    refine card_image_le.trans (le_of_eq ?_)
    rw [oddCnt, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_filter_congr' _ _ (fun c => odd_fiber_iff hmin hf c)
  have key : ∀ s : Finset ((Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f)),
      (∀ l ∈ s, l ∈ ({l ∈ univ.image φ | Odd #{x | φ x = l}} :
        Finset ((Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f)))) →
      #s ≤ #(A ∪ B ∪ C) := fun s hs => card_le_card (fun l hl => hsub (hs l hl))
  refine le_trans (key _ (fun l hl => by
    simp only [mem_filter, mem_image] at hl ⊢
    exact ⟨hl.1, by convert hl.2 using 2; ext; simp⟩)) ?_
  have h2 := card_union_le (A ∪ B) C
  have h3 := card_union_le A B
  have h4 : #B ≤ #{d : G.Dart | d.fst ∈ Tset G f U ∧ d.snd ∈ Sset G f U} := card_image_le
  have h5 : #C ≤ #{p : Σ v : V, Fin (G.degree v - f v) | p.1 ∈ Sset G f U} := card_image_le
  omega
end FFactor

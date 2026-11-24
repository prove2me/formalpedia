-- Prove2me | solution 1 for FFactor.odd_fiber_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:08:45.300027+00:00
-- url     : https://prove2.me/submissions/3323a393-984c-4b8f-a51f-9902b2d56153

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
public import Theorems.Thm_P2M_FFactor_card_filter_congr__c7ce8e64b074
public import Theorems.Thm_FFactor_card_filter_verts
public import Theorems.Thm_FFactor_card_home_fiber
public import Theorems.Thm_FFactor_notMem_U_of_home
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
theorem _root_.solution (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x)
    (hf : ∀ v, f v ≤ G.degree v) (c : (Gr G f U).ConnectedComponent) :
    Odd #{x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts | lab G f U x.1 = .inl c} ↔
    Odd (∑ w ∈ univ.filter (fun w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ) =>
        (G.induce ((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ Tset G f U | G.Adj w t})) := by
  rw [card_filter_verts (U := U) (fun a => lab G f U a = .inl c)]
  obtain ⟨Cs, hCs⟩ : ∃ Cs : Finset V, Cs = (univ.filter
      (fun w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ) =>
      (Gr G f U).connectedComponentMk w = c)).map (Function.Embedding.subtype _) := ⟨_, rfl⟩
  have hmem : ∀ r, r ∈ Cs ↔ ∃ h : r ∉ Sset G f U ∪ Tset G f U,
      (Gr G f U).connectedComponentMk ⟨r, h⟩ = c := by
    intro r
    simp only [hCs, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
    · rintro ⟨h, hc⟩; exact ⟨⟨r, h⟩, hc, rfl⟩
  have hset : ∀ a, (a ∉ U ∧ lab G f U a = .inl c) ↔ home G f U a ∈ Cs := by
    intro a
    rw [hmem]
    constructor
    · rintro ⟨haU, hlab⟩
      by_cases hh : home G f U a ∈ Sset G f U ∪ Tset G f U
      · exfalso
        rcases a with d | p
        · rw [lab_inl_of_mem hh] at hlab; simp at hlab
        · rw [lab_inr_of_mem hh] at hlab; simp at hlab
      · rw [lab_of_notMem hh] at hlab
        exact ⟨hh, Sum.inl_injective hlab⟩
    · rintro ⟨hh, hc⟩
      refine ⟨notMem_U_of_home (hmin := hmin) hh, ?_⟩
      rw [lab_of_notMem hh, hc]
  rw [card_filter_congr' _ _ hset, card_eq_sum_card_fiberwise (f := home G f U) (t := Cs)
    (fun a ha => by simpa using ha)]
  have hterm : ∀ r ∈ Cs, #{a ∈ ({a | home G f U a ∈ Cs} : Finset (GV G f)) | home G f U a = r} =
      G.degree r + #{t ∈ Tset G f U | G.Adj r t} + (G.degree r - f r) := by
    intro r hr
    obtain ⟨h, -⟩ := (hmem r).mp hr
    rw [← card_home_fiber (notMem_T_of_notMem_union h), filter_filter]
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h'; exact ⟨h' ▸ hr, h'⟩
  rw [sum_congr rfl hterm]
  have hsum : ∑ r ∈ Cs, (G.degree r + #{t ∈ Tset G f U | G.Adj r t} + (G.degree r - f r)) =
      ∑ w ∈ univ.filter (fun w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ) =>
        (Gr G f U).connectedComponentMk w = c),
      (G.degree w + #{t ∈ Tset G f U | G.Adj w t} + (G.degree w - f w)) := by
    rw [hCs, sum_map]; rfl
  rw [hsum]
  have hsplit : ∀ w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ),
      G.degree w + #{t ∈ Tset G f U | G.Adj w t} + (G.degree w - f w) =
      (f w + #{t ∈ Tset G f U | G.Adj w t}) + 2 * (G.degree w - f w) := by
    intro w; have := hf w; omega
  rw [sum_congr rfl (fun w _ => hsplit w), sum_add_distrib, ← mul_sum]
  have key : ∀ A B : ℕ, Odd (A + 2 * B) ↔ Odd A := fun A B => by
    simp only [Nat.odd_iff]; omega
  exact key _ _
end FFactor

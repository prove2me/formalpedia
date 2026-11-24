-- Prove2me | solution 1 for FFactor.exists_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:54:58.913858+00:00
-- url     : https://prove2.me/submissions/bf97d118-02da-4dac-8925-24699e8896a3

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorNec
public import Theorems.Thm_FFactor_even_sum_card_adj
public import Theorems.Thm_FFactor_mem_compl_union_iff

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical
namespace FFactor
theorem _root_.solution (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V)
    (c : (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).ConnectedComponent)
    (hc : Odd (∑ w ∈ univ.filter (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) =>
        (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ T | G.Adj w t}))) :
    ∃ w : ↥(((S ∪ T : Finset V) : Set V)ᶜ),
      (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c ∧
      ((∃ z ∈ S, H.Adj w z) ∨ (∃ t ∈ T, G.Adj w t ∧ ¬H.Adj w t)) := by
  by_contra hne
  push Not at hne
  let Cset : Finset V := (univ.filter (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) =>
      (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c)).map
      (Function.Embedding.subtype _)
  have hmem : ∀ u (hu : u ∈ ((S ∪ T : Finset V) : Set V)ᶜ),
      u ∈ Cset ↔ (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk ⟨u, hu⟩ = c := by
    intro u hu
    simp only [Cset, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro h; exact ⟨⟨u, hu⟩, h, rfl⟩
  have hmem' : ∀ u ∈ Cset, ∃ hu : u ∈ ((S ∪ T : Finset V) : Set V)ᶜ,
      (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk ⟨u, hu⟩ = c := by
    intro u hu
    simp only [Cset, mem_map, mem_filter, mem_univ, true_and,
      Function.Embedding.coe_subtype] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    exact ⟨w.2, hw⟩
  have hCsum : ∑ w ∈ Cset, (f w + #{t ∈ T | G.Adj w t}) =
      ∑ w ∈ univ.filter (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) =>
        (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ T | G.Adj w t}) := sum_map _ _ _
  rw [← hCsum] at hc
  have hsplit : ∀ w ∈ Cset, f w + #{t ∈ T | G.Adj w t} =
      #{u ∈ Cset | H.Adj w u} + 2 * #{t ∈ T | G.Adj w t} := by
    intro w hw
    obtain ⟨hwc, hwcc⟩ := hmem' w hw
    have hne' := hne ⟨w, hwc⟩ hwcc
    rw [← hdeg w]
    have heq : ({u | H.Adj w u} : Finset V) =
        {t ∈ T | G.Adj w t} ∪ {u ∈ Cset | H.Adj w u} := by
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · intro hu
        by_cases huT : u ∈ T
        · exact Or.inl ⟨huT, hHG hu⟩
        · have huS : u ∉ S := fun h => hne'.1 u h hu
          have hu' : u ∈ ((S ∪ T : Finset V) : Set V)ᶜ := mem_compl_union_iff.mpr ⟨huS, huT⟩
          refine Or.inr ⟨(hmem u hu').mpr ?_, hu⟩
          rw [← hwcc]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj
            (by simpa using hHG hu)).symm
      · rintro (⟨huT, hu⟩ | ⟨_, hu⟩)
        · exact hne'.2 u huT hu
        · exact hu
    rw [heq, card_union_of_disjoint]
    · ring
    · rw [Finset.disjoint_left]
      intro u hu hu'
      obtain ⟨hu'', _⟩ := hmem' u (mem_filter.mp hu').1
      exact (mem_compl_union_iff.mp hu'').2 (mem_filter.mp hu).1
  rw [sum_congr rfl hsplit, sum_add_distrib, ← mul_sum] at hc
  exact (Nat.not_even_iff_odd.mpr hc) ((even_sum_card_adj H Cset).add (even_two_mul _))
end FFactor

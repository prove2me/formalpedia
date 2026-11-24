-- Prove2me | solution 1 for FFactor.oddCnt_le_card_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:02:31.61879+00:00
-- url     : https://prove2.me/submissions/ccfeb38b-8798-428c-b9d0-a9474ddb8677

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorNec
public import Theorems.Thm_FFactor_mem_compl_union_iff
public import Theorems.Thm_FFactor_exists_witness

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical
namespace FFactor
theorem _root_.solution (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V) :
    oddCnt G f S T ≤ #{p ∈ (univ \ (S ∪ T)) ×ˢ (univ : Finset V) |
      (p.2 ∈ S ∧ H.Adj p.1 p.2) ∨ (p.2 ∈ T ∧ G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2)} := by
  set G' := G.induce ((S ∪ T : Finset V) : Set V)ᶜ
  set Z := ({p ∈ (univ \ (S ∪ T)) ×ˢ (univ : Finset V) |
      (p.2 ∈ S ∧ H.Adj p.1 p.2) ∨ (p.2 ∈ T ∧ G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2)} : Finset (V × V))
  have hex : ∀ c : {c : G'.ConnectedComponent // Odd (∑ w ∈ univ.filter
      (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) => G'.connectedComponentMk w = c),
        (f w + #{t ∈ T | G.Adj w t}))},
      ∃ p ∈ Z, ∃ h : p.1 ∈ ((S ∪ T : Finset V) : Set V)ᶜ,
        G'.connectedComponentMk ⟨p.1, h⟩ = c.1 := by
    intro c
    obtain ⟨w, hw, hwit⟩ := exists_witness G H hHG f hdeg S T c.1 c.2
    have hw2 := mem_compl_union_iff.mp w.2
    rcases hwit with ⟨z, hz, hHz⟩ | ⟨t, ht, hGt, hHt⟩
    · refine ⟨(w.1, z), ?_, w.2, hw⟩
      simp only [Z, mem_filter, mem_product, mem_sdiff, mem_univ, mem_union, true_and]
      exact ⟨by tauto, Or.inl ⟨hz, hHz⟩⟩
    · refine ⟨(w.1, t), ?_, w.2, hw⟩
      simp only [Z, mem_filter, mem_product, mem_sdiff, mem_univ, mem_union, true_and]
      exact ⟨by tauto, Or.inr ⟨ht, hGt, hHt⟩⟩
  let g : {c : G'.ConnectedComponent // Odd (∑ w ∈ univ.filter
      (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) => G'.connectedComponentMk w = c),
        (f w + #{t ∈ T | G.Adj w t}))} → Z :=
    fun c => ⟨Classical.choose (hex c), (Classical.choose_spec (hex c)).1⟩
  have hg : Function.Injective g := by
    intro c d hcd
    have hc := (Classical.choose_spec (hex c)).2
    have hd := (Classical.choose_spec (hex d)).2
    have e : Classical.choose (hex c) = Classical.choose (hex d) := congrArg Subtype.val hcd
    obtain ⟨h1, h1'⟩ := hc
    obtain ⟨h2, h2'⟩ := hd
    apply Subtype.ext
    rw [← h1', ← h2']
    congr 2
    rw [e]
  have := Nat.card_le_card_of_injective g hg
  simpa [Nat.card_eq_fintype_card, oddCnt] using this
end FFactor

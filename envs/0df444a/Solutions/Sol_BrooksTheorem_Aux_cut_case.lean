-- Prove2me | solution 1 for BrooksTheorem.Aux.cut_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:41:13.961274+00:00
-- url     : https://prove2.me/submissions/596cfac2-3880-45ad-b2a3-78133f1491e8

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
public import Theorems.Thm_BrooksTheorem_Aux_Proper_comp
public import Theorems.Thm_BrooksTheorem_Aux_glue
public import Theorems.Thm_BrooksTheorem_Aux_colour_restr
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb


attribute [local simp] BrooksTheorem.Aux.restr_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution {k : ℕ} {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) (B : Set V) {x z y0 b bn : V}
    (hxz : x ≠ z) (hxB : x ∉ B) (hxy : H.Adj x y0)
    (hBedge : ∀ u ∈ B, ∀ v, H.Adj u v → v ∈ B ∨ v = z) (hb : b ∈ B) (hbn : H.Adj b bn) :
    ∃ g : V → Fin k, Proper H g := by
  obtain ⟨c1, h1⟩ := colour_restr ih hdeg hcf Bᶜ hbn (by simpa using hb)
  obtain ⟨c2, h2⟩ := colour_restr ih hdeg hcf {v | v ∈ B ∨ v = z} hxy
    (by simp [hxB, hxz])
  refine glue H Bᶜ {v | v ∈ B ∨ v = z} ?_ c1 (Equiv.swap (c2 z) (c1 z) ∘ c2) h1
    (h2.comp _) ?_
  · intro u v h
    by_cases hu : u ∈ B
    · exact Or.inr ⟨Or.inl hu, hBedge u hu v h⟩
    · by_cases hv : v ∈ B
      · exact Or.inr ⟨hBedge v hv u h.symm, Or.inl hv⟩
      · exact Or.inl ⟨hu, hv⟩
  · intro v hv1 hv2
    rcases hv2 with hv2 | rfl
    · exact absurd hv2 hv1
    · simp
end BrooksTheorem.Aux

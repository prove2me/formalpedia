-- Prove2me | solution 1 for Erdos919.shift_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:48.313094+00:00
-- url     : https://prove2.me/submissions/f9881a4e-6180-47be-9b14-4200b7433586

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_shift_adj

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
variable (I : Type*) [LinearOrder I]
variable {I}
namespace Erdos919
theorem _root_.solution {α : Type*} (c : (shift I).Coloring α) : Function.Injective
    (fun b : I => {a : α | ∃ g : I, ∃ h : b < g, c ⟨(b, g), h⟩ = a}) := by
  have key : ∀ b b' : I, b < b' →
      {a : α | ∃ g : I, ∃ h : b < g, c ⟨(b, g), h⟩ = a} ≠
      {a : α | ∃ g : I, ∃ h : b' < g, c ⟨(b', g), h⟩ = a} := by
    intro b b' hlt hS
    have hmem : c ⟨(b, b'), hlt⟩ ∈ {a : α | ∃ g : I, ∃ h : b < g, c ⟨(b, g), h⟩ = a} :=
      ⟨b', hlt, rfl⟩
    rw [hS] at hmem
    obtain ⟨g, hg, hc⟩ := hmem
    exact c.valid (show (shift I).Adj ⟨(b, b'), hlt⟩ ⟨(b', g), hg⟩ from shift_adj.2 (Or.inl rfl)) hc.symm
  intro b b' hS
  rcases lt_trichotomy b b' with h | h | h
  · exact absurd hS (key _ _ h)
  · exact h
  · exact absurd hS.symm (key _ _ h)
end Erdos919

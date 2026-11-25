-- Prove2me | solution 1 for Erdos919.blowup_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:25.832934+00:00
-- url     : https://prove2.me/submissions/f14521e4-7677-4269-b656-bddd6c439f4c

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
variable {I : Type*} [LinearOrder I]
namespace Erdos919
theorem _root_.solution {H : SimpleGraph I} {α : Type*}
    (hfib : ∀ d : I → α, ∃ a, ∀ x, ∃ y, x ≤ y ∧ d y = a)
    (c : (blowup H).Coloring α) : Nonempty (H.Coloring α) := by
  choose f hf using fun ξ : I => hfib (fun η => c (ξ, η))
  have key : ∀ ξ ξ', ξ < ξ' → H.Adj ξ ξ' → f ξ = f ξ' → False := by
    intro ξ ξ' hlt hadj heq
    obtain ⟨y, -, hy⟩ := hf ξ' ξ'
    obtain ⟨η, hη, hηc⟩ := hf ξ ξ'
    have hA : (blowup H).Adj (ξ, η) (ξ', y) := blowup_adj.2 (Or.inl ⟨hlt, hadj, hη⟩)
    have h1 : c (ξ, η) = f ξ := hηc
    have h2 : c (ξ', y) = f ξ' := hy
    exact c.valid hA (by rw [h1, h2, heq])
  refine ⟨Coloring.mk f ?_⟩
  intro ξ ξ' hadj heq
  rcases lt_trichotomy ξ ξ' with h | h | h
  · exact key _ _ h hadj heq
  · exact H.ne_of_adj hadj h
  · exact key _ _ h hadj.symm heq.symm
end Erdos919

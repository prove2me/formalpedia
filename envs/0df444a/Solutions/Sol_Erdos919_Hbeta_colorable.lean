-- Prove2me | solution 1 for Erdos919.Hbeta_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:31.891029+00:00
-- url     : https://prove2.me/submissions/a9804120-02f6-4362-8f5e-c799b98eaa7d

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
theorem _root_.solution [WellFoundedLT I] {H : SimpleGraph I}
    (hinit : ∀ a : I, ∃ c : I → ℕ, ∀ ξ ξ', ξ < a → ξ' < a → H.Adj ξ ξ' → c ξ ≠ c ξ')
    (β : I → I) (hclub : ∀ a : I, ∃ δ, a < δ ∧ ∀ ζ < δ, β ζ ≤ δ) :
    ∃ c₁ : I → ℕ, ∀ ξ ξ', ξ < ξ' → H.Adj ξ ξ' → ξ' < β ξ → c₁ ξ ≠ c₁ ξ' := by
  classical
  let C : Set I := {δ | ∀ ζ < δ, β ζ ≤ δ}
  have hne : ∀ a, {δ | a < δ ∧ δ ∈ C}.Nonempty := fun a => by
    obtain ⟨δ, h1, h2⟩ := hclub a
    exact ⟨δ, h1, h2⟩
  let ν : I → I := fun a => WellFounded.min wellFounded_lt _ (hne a)
  have hν1 : ∀ a, a < ν a ∧ ν a ∈ C := fun a => WellFounded.min_mem _ _ (hne a)
  have hν2 : ∀ a δ, a < δ → δ ∈ C → ν a ≤ δ := fun a δ h1 h2 =>
    not_lt.1 (WellFounded.not_lt_min wellFounded_lt {δ | a < δ ∧ δ ∈ C} ⟨h1, h2⟩)
  choose c hc using hinit
  refine ⟨fun ξ => c (ν ξ) ξ, ?_⟩
  intro ξ ξ' hlt hadj hβ
  have h1 := hν1 ξ
  have hξ' : ξ' < ν ξ := lt_of_lt_of_le hβ (h1.2 ξ h1.1)
  have heq : ν ξ' = ν ξ :=
    le_antisymm (hν2 ξ' (ν ξ) hξ' h1.2) (hν2 ξ (ν ξ') (hlt.trans (hν1 ξ').1) (hν1 ξ').2)
  show c (ν ξ) ξ ≠ c (ν ξ') ξ'
  rw [heq]
  exact hc (ν ξ) ξ ξ' h1.1 hξ' hadj
end Erdos919

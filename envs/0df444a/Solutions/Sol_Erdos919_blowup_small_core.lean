-- Prove2me | solution 1 for Erdos919.blowup_small_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:30.897307+00:00
-- url     : https://prove2.me/submissions/ba229422-fb25-4f62-835d-95b10d470414

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
theorem _root_.solution {H : SimpleGraph I} (X : Set (I × I)) (ξ₀ : I) (β : I → I)
    (hβ : ∀ p ∈ X, ξ₀ ≤ p.1 → p.2 < β p.1)
    (c₀ : I → ℕ) (hc₀ : ∀ ξ ξ', ξ < ξ₀ → ξ' < ξ₀ → H.Adj ξ ξ' → c₀ ξ ≠ c₀ ξ')
    (c₁ : I → ℕ) (hc₁ : ∀ ξ ξ', ξ < ξ' → H.Adj ξ ξ' → ξ' < β ξ → c₁ ξ ≠ c₁ ξ') :
    ColorableOn (blowup H) X (Bool × ℕ) := by
  classical
  let col : I × I → Bool × ℕ := fun p => if p.1 < ξ₀ then (false, c₀ p.1) else (true, c₁ p.1)
  have key : ∀ p ∈ X, ∀ q ∈ X, p.1 < q.1 → H.Adj p.1 q.1 → q.1 ≤ p.2 → col p ≠ col q := by
    intro p hp q hq hlt hadj hle h
    simp only [col] at h
    split_ifs at h with h1 h2 h2
    · exact hc₀ _ _ h1 h2 hadj (Prod.ext_iff.1 h).2
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact hc₁ _ _ hlt hadj (lt_of_le_of_lt hle (hβ p hp (not_lt.1 h1)))
        (Prod.ext_iff.1 h).2
  refine ⟨col, ?_⟩
  intro p hp q hq hpq
  rcases blowup_adj.1 hpq with ⟨hlt, hadj, hle⟩ | ⟨hlt, hadj, hle⟩
  · exact key p hp q hq hlt hadj hle
  · exact fun h => key q hq p hp hlt hadj hle h.symm
end Erdos919

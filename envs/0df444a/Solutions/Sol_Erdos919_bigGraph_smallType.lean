-- Prove2me | solution 1 for Erdos919.bigGraph_smallType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:40:40.971655+00:00
-- url     : https://prove2.me/submissions/d488925e-ac34-4e8c-b364-cc8badf5d282

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_ColorableOn_toNat
public import Theorems.Thm_Erdos919_blowup_small_core
public import Theorems.Thm_Erdos919_Hbeta_colorable
public import Theorems.Thm_Erdos919_mk_Iio_W
public import Theorems.Thm_Erdos919_exists_closure_point
public import Theorems.Thm_Erdos919_rows_bounded

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution (H : SimpleGraph W.{u}) (hH : SmallCardCC H) :
    SmallTypeCC (bigGraph H) := by
  intro X hX
  rw [← typeLT_lex] at hX
  obtain ⟨ξ₀, hξ₀⟩ := rows_bounded X hX
  have hb : ∀ ξ : W.{u}, ∃ b : W.{u}, ∀ η, ξ₀ ≤ ξ → b ≤ η → toLex (ξ, η) ∉ X := by
    intro ξ
    by_cases hF : ∀ x, ∃ η, x ≤ η ∧ toLex (ξ, η) ∈ X
    · exact ⟨ξ, fun _ h => absurd (hξ₀ ξ hF) (not_lt.2 h)⟩
    · push Not at hF
      obtain ⟨b, hb⟩ := hF
      exact ⟨b, fun η _ hη hmem => hb η hη hmem⟩
  choose β hβ using hb
  have hβ' : ∀ p ∈ ofLex '' X, ξ₀ ≤ p.1 → p.2 < β p.1 := by
    rintro _ ⟨q, hq, rfl⟩ h
    by_contra hlt
    exact hβ _ _ h (not_lt.1 hlt) (by simpa using hq)
  have hinit : ∀ a : W.{u}, ∃ c : W.{u} → ℕ,
      ∀ ξ ξ', ξ < a → ξ' < a → H.Adj ξ ξ' → c ξ ≠ c ξ' := by
    intro a
    obtain ⟨c, hc⟩ := hH (Iio a) (mk_Iio_W a)
    exact ⟨c, fun ξ ξ' h1 h2 hadj => hc ξ h1 ξ' h2 hadj⟩
  obtain ⟨c₀, hc₀⟩ := hinit ξ₀
  obtain ⟨c₁, hc₁⟩ := Hbeta_colorable hinit β (exists_closure_point β)
  obtain ⟨c, hc⟩ := (blowup_small_core (ofLex '' X) ξ₀ β hβ' c₀ hc₀ c₁ hc₁).toNat
  exact ⟨fun p => c (ofLex p), fun x hx y hy hxy => hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy⟩
end Erdos919

-- Prove2me | solution 1 for FourColourRSST.Ring.consistent_union_eqClass
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:44:49.38938+00:00
-- url     : https://prove2.me/submissions/99700973-19e9-4c5d-9063-5c45e7cd9cff

import Mathlib
import Definitions.Def_FourColourRSST_Ring_Setting

open FourColourRSST.Ring

private theorem fits_perm {k : ℕ} (θ : SignType) (κ : EdgeColouring k)
    (M : Set (SignedMatch k)) (σ : Equiv.Perm SignType) (hσ : σ θ = θ)
    (h : Fits θ κ M) : Fits θ (fun e => σ (κ e)) M := by
  constructor
  · rw [h.1]
    ext e
    change (κ e ≠ θ) ↔ (σ (κ e) ≠ θ)
    have he : σ (κ e) = θ ↔ κ e = θ := by
      constructor
      · intro h; exact σ.injective (h.trans hσ.symm)
      · intro h; exact (congrArg σ h).trans hσ
    exact not_congr he.symm
  · intro p hp e f hef
    rw [σ.injective.eq_iff]
    exact h.2 p hp e f hef

private theorem colour_closed {k : ℕ} [NeZero k]
    (C : Set (EdgeColouring k)) (hC : Consistent C)
    (σ : Equiv.Perm SignType) : ∀ κ ∈ C, (fun e => σ (κ e)) ∈ C := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simpa using (fun κ (hκ : κ ∈ C) => hκ)
  | swap_mul σ a b hab ih =>
    intro κ hκ
    have hex : ∃ θ : SignType, Equiv.swap a b θ = θ := by
      cases a <;> cases b <;> decide
    obtain ⟨θ, hθ⟩ := hex
    obtain ⟨M, _, hfit, hall⟩ := hC _ (ih κ hκ) θ
    exact hall _ (fits_perm θ _ M (Equiv.swap a b) hθ hfit)

theorem solution {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (C : Set (EdgeColouring k)) (hC : Consistent C) :
    ∀ κ ∈ C, eqClass κ ⊆ C := by
  intro κ hκ κ' hκ'
  obtain ⟨σ, hσ⟩ := hκ'
  have heq : κ' = fun e => σ (κ e) := funext hσ
  rw [heq]
  exact colour_closed C hC σ κ hκ

#print axioms solution

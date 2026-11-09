-- Prove2me | solution 1 for BeliefDominance.le_isPreorder
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:06:56.909806+00:00
-- url     : https://prove2.me/submissions/d84b1c92-ae8a-496f-9d7a-5efbd92478c7

import Mathlib
import Definitions.Def_BeliefDominance_Problem

namespace Aux_BDpre
open BeliefDominance

theorem key {ι : Type*} (S : Set ι) (g g' : ι → ℝ) :
    ((∀ f ∈ S, g' f ≥ g f) ∧ ∃ f ∈ S, g' f > g f) ∨ (∀ f ∈ S, g' f = g f) ↔
      ∀ f ∈ S, g f ≤ g' f := by
  constructor
  · rintro (⟨h1, _⟩ | h)
    · exact fun f hf => h1 f hf
    · exact fun f hf => (h f hf).ge
  · intro h
    by_cases hex : ∃ f ∈ S, g' f > g f
    · exact Or.inl ⟨fun f hf => h f hf, hex⟩
    · right
      push_neg at hex
      exact fun f hf => le_antisymm (hex f hf) (h f hf)

theorem gen {α ι : Type*} (S : Set ι) (val : α → ι → ℝ) (L Dm Id : α → α → Prop)
    (hD : ∀ x' x, Dm x' x ↔ (∀ f ∈ S, val x' f ≥ val x f) ∧ ∃ f ∈ S, val x' f > val x f)
    (hI : ∀ x' x, Id x' x ↔ ∀ f ∈ S, val x' f = val x f)
    (hL : ∀ x x', L x x' ↔ Dm x' x ∨ Id x' x) :
    (∀ x, L x x) ∧ (∀ x x' x'', L x x' → L x' x'' → L x x'') ∧
      (∀ x x', Dm x' x ↔ strictPart L x x') ∧ (∀ x x', Id x' x ↔ L x x' ∧ L x' x) := by
  have hle : ∀ x x', L x x' ↔ ∀ f ∈ S, val x f ≤ val x' f := by
    intro x x'
    rw [hL, hD, hI]
    exact key S (val x) (val x')
  refine ⟨fun x => (hle x x).mpr fun f _ => le_refl _, fun x x' x'' h1 h2 => ?_,
    fun x x' => ?_, fun x x' => ?_⟩
  · rw [hle] at h1 h2 ⊢
    exact fun f hf => (h1 f hf).trans (h2 f hf)
  · unfold strictPart
    rw [hle, hle, hD]
    constructor
    · rintro ⟨h1, f, hf, h2⟩
      exact ⟨fun f hf => h1 f hf, fun h => absurd (h f hf) (not_le.mpr h2)⟩
    · rintro ⟨h1, h2⟩
      push_neg at h2
      obtain ⟨f, hf, h3⟩ := h2
      exact ⟨fun f hf => h1 f hf, f, hf, h3⟩
  · rw [hle, hle, hI]
    constructor
    · intro h
      exact ⟨fun f hf => (h f hf).ge, fun f hf => (h f hf).le⟩
    · rintro ⟨h1, h2⟩
      exact fun f hf => le_antisymm (h2 f hf) (h1 f hf)

end Aux_BDpre

open BeliefDominance in
theorem solution {A₁ A₂ Y Z : Type*} (P : Problem A₁ A₂ Y Z) :
    ((∀ x, P.le x x) ∧
      (∀ x x' x'', P.le x x' → P.le x' x'' → P.le x x'') ∧
      (∀ x x', P.Dominates x' x ↔ strictPart P.le x x') ∧
      (∀ x x', P.Indiff x' x ↔ P.le x x' ∧ P.le x' x)) ∧
    ∀ (x₁ : A₁) (y : Y),
      (∀ a, P.le₂ x₁ y a a) ∧
      (∀ a a' a'', P.le₂ x₁ y a a' → P.le₂ x₁ y a' a'' → P.le₂ x₁ y a a'') ∧
      (∀ a a', P.Dominates₂ x₁ y a' a ↔ strictPart (P.le₂ x₁ y) a a') ∧
      (∀ a a', P.Indiff₂ x₁ y a' a ↔ P.le₂ x₁ y a a' ∧ P.le₂ x₁ y a' a) := by
  refine ⟨Aux_BDpre.gen P.Φ P.V P.le P.Dominates P.Indiff (fun _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl), fun x₁ y => ?_⟩
  exact Aux_BDpre.gen (P.Φy y) (fun a f => P.V₂ x₁ a y f) (P.le₂ x₁ y) (P.Dominates₂ x₁ y)
    (P.Indiff₂ x₁ y) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)

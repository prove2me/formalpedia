-- Prove2me | solution 1 for BeliefDominance.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:14:53.933883+00:00
-- url     : https://prove2.me/submissions/2a91e75c-4e79-41ec-b11b-d07b82f4333e

import Mathlib
import Definitions.Def_BeliefDominance_DecisionSpace

open BeliefDominance in
theorem solution {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le : A₁ × (Y → A₂) → A₁ × (Y → A₂) → Prop) (le₂ : A₁ → Y → A₂ → A₂ → Prop)
    (h : WeaklyConsistent D le le₂) : ¬ ExhibitsFallacious D le le₂ := by
  classical
  rintro ⟨xs, ⟨hxs, hopt⟩, y, hy⟩
  have hmem : xs.2 y ∈ D.X₂ xs.1 y := hxs.2 y
  obtain ⟨b, hb, hsb⟩ : ∃ b ∈ D.X₂ xs.1 y, strictPart (le₂ xs.1 y) (xs.2 y) b := by
    by_contra hc
    push_neg at hc
    exact hy ⟨hmem, hc⟩
  let x' : A₁ × (Y → A₂) := (xs.1, Function.update xs.2 y b)
  have hx' : x' ∈ D.strategies := by
    refine ⟨hxs.1, fun y' => ?_⟩
    by_cases hy' : y' = y
    · subst hy'
      show Function.update xs.2 y' b y' ∈ D.X₂ xs.1 y'
      rw [Function.update_self]
      exact hb
    · show Function.update xs.2 y b y' ∈ D.X₂ xs.1 y'
      rw [Function.update_of_ne hy']
      exact hxs.2 y'
  have hs' : strictPart (le₂ xs.1 y) (xs.2 y) (x'.2 y) := by
    show strictPart (le₂ xs.1 y) (xs.2 y) (Function.update xs.2 y b y)
    rw [Function.update_self]
    exact hsb
  have := (h xs hxs x' hx' y rfl (fun y' hy' => (Function.update_of_ne hy' b xs.2).symm)).1 hs'
  exact hopt x' hx' this

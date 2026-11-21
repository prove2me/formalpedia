-- Prove2me | solution 1 for Champernowne.card_allWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:31.091861+00:00
-- url     : https://prove2.me/submissions/6aec131c-5dba-470b-86ce-76ce59d666aa

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b k : ℕ) : (allWords b k).card = b ^ k := by
  induction k with
  | zero => simp [allWords]
  | succ k ih =>
    have hdisj : ∀ d₁ ∈ Finset.range b, ∀ d₂ ∈ Finset.range b, d₁ ≠ d₂ →
        Disjoint ((allWords b k).image (d₁ :: ·))
          ((allWords b k).image (d₂ :: ·)) := by
      intro d₁ _ d₂ _ hne
      rw [Finset.disjoint_left]
      rintro l hl₁ hl₂
      obtain ⟨v₁, -, rfl⟩ := Finset.mem_image.mp hl₁
      obtain ⟨v₂, -, heq⟩ := Finset.mem_image.mp hl₂
      injection heq with h1 _
      exact hne h1.symm
    calc (allWords b (k + 1)).card
        = ∑ d ∈ Finset.range b, ((allWords b k).image (d :: ·)).card :=
          Finset.card_biUnion hdisj
    _ = ∑ _d ∈ Finset.range b, (allWords b k).card :=
          Finset.sum_congr rfl fun d _ =>
            Finset.card_image_of_injective _ fun v₁ v₂ h => by injection h
    _ = b ^ (k + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ih, pow_succ']
end Champernowne

-- Prove2me | solution 1 for FuzzyExtractors.ImprovedJS.pLow_unique
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-20T08:40:34.110253+00:00
-- url     : https://prove2.me/submissions/37b91f74-5717-4d98-a161-3c44e259686a

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

open Polynomial

theorem solution {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s)
    (w' : Finset 𝔽) (hw' : w'.card = s) (b : 𝔽 → 𝔽) (p₁ p₂ : 𝔽[X])
    (hdeg₁ : p₁.degree < ((s - t : ℕ) : WithBot ℕ))
    (hdeg₂ : p₂.degree < ((s - t : ℕ) : WithBot ℕ))
    (hagree₁ : 2 * s - t ≤ 2 * (w'.filter fun x => p₁.eval x = b x).card)
    (hagree₂ : 2 * s - t ≤ 2 * (w'.filter fun x => p₂.eval x = b x).card) :
    p₁ = p₂ := by
  classical
  let A := w'.filter fun x => p₁.eval x = b x
  let B := w'.filter fun x => p₂.eval x = b x
  have hUnion : (A ∪ B).card ≤ s := by
    rw [← hw']
    apply Finset.card_le_card
    exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hCount := Finset.card_union_add_card_inter A B
  have hInter : s - t ≤ (A ∩ B).card := by
    change 2 * s - t ≤ 2 * A.card at hagree₁
    change 2 * s - t ≤ 2 * B.card at hagree₂
    omega
  by_contra hp
  have hdiff : p₁ - p₂ ≠ 0 := sub_ne_zero.mpr hp
  have hDegree : (p₁ - p₂).degree < ((s - t : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (degree_sub_le p₁ p₂) (max_lt hdeg₁ hdeg₂)
  have hRoots : (A ∩ B).val ⊆ (p₁ - p₂).roots := by
    intro x hx
    have hxAB : x ∈ A ∩ B := hx
    rcases Finset.mem_inter.mp hxAB with ⟨hxA, hxB⟩
    have hx₁ := (Finset.mem_filter.mp hxA).2
    have hx₂ := (Finset.mem_filter.mp hxB).2
    apply (Polynomial.mem_roots hdiff).mpr
    change (p₁ - p₂).eval x = 0
    rw [eval_sub, hx₁, hx₂, sub_self]
  have hCard := Polynomial.card_le_degree_of_subset_roots hRoots
  have hNatDegree : (p₁ - p₂).natDegree < s - t := by
    rw [degree_eq_natDegree hdiff] at hDegree
    exact WithBot.coe_lt_coe.mp hDegree
  omega

#print axioms solution

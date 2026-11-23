-- Prove2me | solution 1 for FasterWCTFPTAS.Main.smith_rule
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:25:57.227956+00:00
-- url     : https://prove2.me/submissions/f432d685-b34d-4649-bd14-a7f61a5454d2

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Scheduling

set_option autoImplicit false

open FasterWCTFPTAS.Main
open Finset

namespace SmithRuleAux

lemma smith_cost_eq_sum {n m : ℕ} (p w : Fin n → ℝ) (σ : Fin n → Fin m) :
    smithCost p w σ =
      ∑ j : Fin n, ∑ i : Fin n,
        if σ i = σ j ∧ SmithBefore p w i j then w j * p i else 0 := by
  unfold smithCost smithCompletion
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

lemma cost_eq_sum {n m : ℕ} (p w : Fin n → ℝ) (σ : Fin n → Fin m) (ρ : Fin n ≃ Fin n) :
    cost p w σ ρ =
      ∑ j : Fin n, ∑ i : Fin n,
        if σ i = σ j ∧ ρ i ≤ ρ j then w j * p i else 0 := by
  unfold cost completion
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

lemma pair_le {n m : ℕ} (p w : Fin n → ℝ) (σ : Fin n → Fin m) (ρ : Fin n ≃ Fin n)
    (i j : Fin n) :
    (if σ i = σ j ∧ SmithBefore p w i j then w j * p i else 0) +
      (if σ j = σ i ∧ SmithBefore p w j i then w i * p j else 0) ≤
    (if σ i = σ j ∧ ρ i ≤ ρ j then w j * p i else 0) +
      (if σ j = σ i ∧ ρ j ≤ ρ i then w i * p j else 0) := by
  by_cases hσ : σ i = σ j
  · have hσ' : σ j = σ i := hσ.symm
    by_cases hij : i = j
    · subst hij
      have hs : SmithBefore p w i i := Or.inr ⟨rfl, le_rfl⟩
      simp [hs]
    · have hρ_ne : ρ i ≠ ρ j := fun h => hij (ρ.injective h)
      have hρ_cases : (ρ i ≤ ρ j ∧ ¬ ρ j ≤ ρ i) ∨ (¬ ρ i ≤ ρ j ∧ ρ j ≤ ρ i) := by
        rcases lt_trichotomy (ρ i) (ρ j) with hlt | heq | hgt
        · exact Or.inl ⟨le_of_lt hlt, not_le_of_gt hlt⟩
        · exact absurd heq hρ_ne
        · exact Or.inr ⟨not_le_of_gt hgt, le_of_lt hgt⟩
      rcases lt_trichotomy (w j * p i) (w i * p j) with hwlt | hweq | hwgt
      · have hs1 : SmithBefore p w i j := Or.inl hwlt
        have hs2 : ¬ SmithBefore p w j i := by
          rintro (h | ⟨h, _⟩) <;> linarith
        rw [if_pos ⟨hσ, hs1⟩, if_neg (fun h => hs2 h.2)]
        rcases hρ_cases with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
        · rw [if_pos ⟨hσ, hr1⟩, if_neg (fun h => hr2 h.2)]
        · rw [if_neg (fun h => hr1 h.2), if_pos ⟨hσ', hr2⟩]; linarith
      · rcases lt_trichotomy i j with hilt | hieq | higt
        · have hs1 : SmithBefore p w i j := Or.inr ⟨hweq, le_of_lt hilt⟩
          have hs2 : ¬ SmithBefore p w j i := by
            rintro (h | ⟨_, hle⟩)
            · linarith
            · exact not_le_of_gt hilt hle
          rw [if_pos ⟨hσ, hs1⟩, if_neg (fun h => hs2 h.2)]
          rcases hρ_cases with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
          · rw [if_pos ⟨hσ, hr1⟩, if_neg (fun h => hr2 h.2)]
          · rw [if_neg (fun h => hr1 h.2), if_pos ⟨hσ', hr2⟩]; linarith
        · exact absurd hieq hij
        · have hs2 : SmithBefore p w j i := Or.inr ⟨hweq.symm, le_of_lt higt⟩
          have hs1 : ¬ SmithBefore p w i j := by
            rintro (h | ⟨_, hle⟩)
            · linarith
            · exact not_le_of_gt higt hle
          rw [if_neg (fun h => hs1 h.2), if_pos ⟨hσ', hs2⟩]
          rcases hρ_cases with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
          · rw [if_pos ⟨hσ, hr1⟩, if_neg (fun h => hr2 h.2)]; linarith
          · rw [if_neg (fun h => hr1 h.2), if_pos ⟨hσ', hr2⟩]
      · have hs2 : SmithBefore p w j i := Or.inl hwgt
        have hs1 : ¬ SmithBefore p w i j := by
          rintro (h | ⟨h, _⟩) <;> linarith
        rw [if_neg (fun h => hs1 h.2), if_pos ⟨hσ', hs2⟩]
        rcases hρ_cases with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
        · rw [if_pos ⟨hσ, hr1⟩, if_neg (fun h => hr2 h.2)]; linarith
        · rw [if_neg (fun h => hr1 h.2), if_pos ⟨hσ', hr2⟩]
  · have hσ' : σ j ≠ σ i := Ne.symm hσ
    rw [if_neg (fun h => hσ h.1), if_neg (fun h => hσ' h.1),
        if_neg (fun h => hσ h.1), if_neg (fun h => hσ' h.1)]

end SmithRuleAux

theorem solution {n m : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (σ : Fin n → Fin m) (ρ : Fin n ≃ Fin n) :
    smithCost p w σ ≤ cost p w σ ρ := by
  have _ := hp
  have _ := hw
  have h2 : 2 * smithCost p w σ ≤ 2 * cost p w σ ρ := by
    rw [SmithRuleAux.smith_cost_eq_sum, SmithRuleAux.cost_eq_sum]
    have hsymS :
        2 * (∑ j : Fin n, ∑ i : Fin n,
          if σ i = σ j ∧ SmithBefore p w i j then w j * p i else 0) =
        ∑ i : Fin n, ∑ j : Fin n,
          ((if σ i = σ j ∧ SmithBefore p w i j then w j * p i else 0) +
           (if σ j = σ i ∧ SmithBefore p w j i then w i * p j else 0)) := by
      rw [two_mul]
      conv_lhs =>
        arg 1
        rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
    have hsymR :
        2 * (∑ j : Fin n, ∑ i : Fin n,
          if σ i = σ j ∧ ρ i ≤ ρ j then w j * p i else 0) =
        ∑ i : Fin n, ∑ j : Fin n,
          ((if σ i = σ j ∧ ρ i ≤ ρ j then w j * p i else 0) +
           (if σ j = σ i ∧ ρ j ≤ ρ i then w i * p j else 0)) := by
      rw [two_mul]
      conv_lhs =>
        arg 1
        rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
    rw [hsymS, hsymR]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact SmithRuleAux.pair_le p w σ ρ i j
  linarith

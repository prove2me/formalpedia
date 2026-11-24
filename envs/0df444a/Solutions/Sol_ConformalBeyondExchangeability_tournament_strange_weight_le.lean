-- Prove2me | solution 1 for ConformalBeyondExchangeability.tournament_strange_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T15:18:18.706258+00:00
-- url     : https://prove2.me/submissions/0972a215-cb46-4890-80c8-08c29e463038

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory
namespace ConformalBeyondExchangeability


theorem tournament_strange_weight_le {n : ℕ} (p : Fin (n + 1) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ∑ i ∈ tournamentStrangeSet p α r, p i ≤ 2 * α := by
  classical
  set S := tournamentStrangeSet p α r with hS
  set P := ∑ i ∈ S, p i with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun i _ => hp i)
  have hPc : ∑ i ∈ Sᶜ, p i = 1 - P := by
    rw [← hp1, ← Finset.sum_add_sum_compl S p]; ring
  set f : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j => p i * (if r j i < r i j then p j else 0) with hf
  have hmem : ∀ i ∈ S, 1 - α ≤ ∑ j, (if r j i < r i j then p j else 0) := by
    intro i hi
    simp only [hS, tournamentStrangeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi
  have h1 : (1 - α) * P ≤ ∑ i ∈ S, ∑ j, f i j := by
    rw [hP, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    simp only [hf, ← Finset.mul_sum]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hmem i hi) (hp i)
  have hsplit : ∑ i ∈ S, ∑ j, f i j = ∑ i ∈ S, ∑ j ∈ S, f i j + ∑ i ∈ S, ∑ j ∈ Sᶜ, f i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_add_sum_compl]
  have hfle : ∀ i j, f i j ≤ p i * p j := by
    intro i j
    simp only [hf]
    split_ifs
    · exact le_refl _
    · rw [mul_zero]; exact mul_nonneg (hp i) (hp j)
  have h2 : ∑ i ∈ S, ∑ j ∈ Sᶜ, f i j ≤ P * (1 - P) := by
    calc _ ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, p i * p j :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hfle i j
      _ = P * (1 - P) := by rw [← hPc, hP, Finset.sum_mul_sum]
  have h3 : 2 * ∑ i ∈ S, ∑ j ∈ S, f i j ≤ P * P := by
    have hsw : ∑ i ∈ S, ∑ j ∈ S, f i j = ∑ i ∈ S, ∑ j ∈ S, f j i := Finset.sum_comm
    have hpair : ∀ i j, f i j + f j i ≤ p i * p j := by
      intro i j
      simp only [hf]
      by_cases h : r j i < r i j
      · have h' : ¬ r i j < r j i := lt_asymm h
        rw [if_pos h, if_neg h']; simp
      · rw [if_neg h]
        split_ifs
        · linarith [mul_comm (p i) (p j)]
        · simp; exact mul_nonneg (hp i) (hp j)
    calc 2 * ∑ i ∈ S, ∑ j ∈ S, f i j
        = ∑ i ∈ S, ∑ j ∈ S, (f i j + f j i) := by
          rw [two_mul]; nth_rewrite 2 [hsw]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib).symm
      _ ≤ ∑ i ∈ S, ∑ j ∈ S, p i * p j :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
      _ = P * P := by rw [hP, Finset.sum_mul_sum]
  nlinarith


end ConformalBeyondExchangeability

open ConformalBeyondExchangeability in
theorem solution {n : ℕ} (p : Fin (n + 1) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ∑ i ∈ tournamentStrangeSet p α r, p i ≤ 2 * α := by
  classical
  set S := tournamentStrangeSet p α r with hS
  set P := ∑ i ∈ S, p i with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun i _ => hp i)
  have hPc : ∑ i ∈ Sᶜ, p i = 1 - P := by
    rw [← hp1, ← Finset.sum_add_sum_compl S p]; ring
  set f : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j => p i * (if r j i < r i j then p j else 0) with hf
  have hmem : ∀ i ∈ S, 1 - α ≤ ∑ j, (if r j i < r i j then p j else 0) := by
    intro i hi
    simp only [hS, tournamentStrangeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi
  have h1 : (1 - α) * P ≤ ∑ i ∈ S, ∑ j, f i j := by
    rw [hP, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    simp only [hf, ← Finset.mul_sum]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hmem i hi) (hp i)
  have hsplit : ∑ i ∈ S, ∑ j, f i j = ∑ i ∈ S, ∑ j ∈ S, f i j + ∑ i ∈ S, ∑ j ∈ Sᶜ, f i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_add_sum_compl]
  have hfle : ∀ i j, f i j ≤ p i * p j := by
    intro i j
    simp only [hf]
    split_ifs
    · exact le_refl _
    · rw [mul_zero]; exact mul_nonneg (hp i) (hp j)
  have h2 : ∑ i ∈ S, ∑ j ∈ Sᶜ, f i j ≤ P * (1 - P) := by
    calc _ ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, p i * p j :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hfle i j
      _ = P * (1 - P) := by rw [← hPc, hP, Finset.sum_mul_sum]
  have h3 : 2 * ∑ i ∈ S, ∑ j ∈ S, f i j ≤ P * P := by
    have hsw : ∑ i ∈ S, ∑ j ∈ S, f i j = ∑ i ∈ S, ∑ j ∈ S, f j i := Finset.sum_comm
    have hpair : ∀ i j, f i j + f j i ≤ p i * p j := by
      intro i j
      simp only [hf]
      by_cases h : r j i < r i j
      · have h' : ¬ r i j < r j i := lt_asymm h
        rw [if_pos h, if_neg h']; simp
      · rw [if_neg h]
        split_ifs
        · linarith [mul_comm (p i) (p j)]
        · simp; exact mul_nonneg (hp i) (hp j)
    calc 2 * ∑ i ∈ S, ∑ j ∈ S, f i j
        = ∑ i ∈ S, ∑ j ∈ S, (f i j + f j i) := by
          rw [two_mul]; nth_rewrite 2 [hsw]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib).symm
      _ ≤ ∑ i ∈ S, ∑ j ∈ S, p i * p j :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
      _ = P * P := by rw [hP, Finset.sum_mul_sum]
  nlinarith


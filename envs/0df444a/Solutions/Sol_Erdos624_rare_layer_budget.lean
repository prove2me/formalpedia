-- Prove2me | solution 1 for Erdos624.rare_layer_budget
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:52.542513+00:00
-- url     : https://prove2.me/submissions/e2548b20-21e6-4dc1-8d08-b6cb8112309d

import Mathlib
open Finset

namespace E624R14R
open Finset Real

lemma binom_exp (k : ℕ) (t : ℝ) :
    ∑ m ∈ range (k + 1), (k.choose m : ℝ) * exp (t * (m - k / 2)) ≤
      2 ^ k * exp (k * t ^ 2 / 8) := by
  have h1 : ∀ m : ℕ, exp (t * (m - k / 2)) = exp t ^ m * exp (-(t / 2)) ^ k := by
    intro m
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]; congr 1; ring
  have h2 : ∑ m ∈ range (k + 1), (k.choose m : ℝ) * exp (t * (m - k / 2)) =
      (exp (-(t / 2)) * (exp t + 1)) ^ k := by
    rw [mul_pow, add_pow, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [h1, one_pow, mul_one]; ring
  have h3 : exp (-(t / 2)) * (exp t + 1) = 2 * cosh (t / 2) := by
    rw [cosh_eq, mul_add, ← exp_add, mul_one]; ring_nf
  rw [h2, h3, mul_pow]
  have h4 : cosh (t / 2) ^ k ≤ exp ((t / 2) ^ 2 / 2) ^ k :=
    pow_le_pow_left₀ (cosh_pos _).le (cosh_le_exp_half_sq _) k
  rw [← exp_nat_mul] at h4
  have h5 : (k : ℝ) * ((t / 2) ^ 2 / 2) = k * t ^ 2 / 8 := by ring
  rw [h5] at h4
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

lemma tail_count (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * ∑ m ∈ (range (k + 1)).filter
      (fun m : ℕ => (k : ℝ) * Real.log k ≤ 2 * ((m : ℝ) - k / 2) ^ 2), (k.choose m : ℝ) ≤
      2 * 2 ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  set w := Real.sqrt (k * Real.log k / 2) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = k * Real.log k / 2 := Real.sq_sqrt (by positivity)
  set t := 4 * w / k with ht
  have ht0 : 0 ≤ t := by positivity
  have hpt : ∀ m ∈ (range (k + 1)).filter
      (fun m : ℕ => (k : ℝ) * Real.log k ≤ 2 * ((m : ℝ) - k / 2) ^ 2),
      (k.choose m : ℝ) ≤ (k.choose m : ℝ) * (exp (-(t * w)) *
        (exp (t * (m - k / 2)) + exp ((-t) * (m - k / 2)))) := by
    intro m hm
    have hc := (mem_filter.1 hm).2
    have habs : w ≤ |(m : ℝ) - k / 2| := by
      rw [← Real.sqrt_sq_eq_abs, hw]
      exact Real.sqrt_le_sqrt (by linarith)
    have hone : 1 ≤ exp (-(t * w)) * (exp (t * (m - k / 2)) + exp ((-t) * (m - k / 2))) := by
      have e1 : exp (t * w) ≤ exp (t * (m - k / 2)) + exp ((-t) * (m - k / 2)) := by
        rcases le_total 0 ((m : ℝ) - k / 2) with h | h
        · rw [abs_of_nonneg h] at habs
          have := exp_le_exp.2 (mul_le_mul_of_nonneg_left habs ht0)
          linarith [exp_pos ((-t) * (m - k / 2))]
        · rw [abs_of_nonpos h] at habs
          have := exp_le_exp.2 (mul_le_mul_of_nonneg_left habs ht0)
          have e : t * -((m : ℝ) - k / 2) = (-t) * (m - k / 2) := by ring
          rw [e] at this
          linarith [exp_pos (t * (m - k / 2))]
      have := mul_le_mul_of_nonneg_left e1 (exp_pos (-(t * w))).le
      rwa [← exp_add, neg_add_cancel, exp_zero] at this
    have := mul_le_mul_of_nonneg_left hone (show (0 : ℝ) ≤ k.choose m by positivity)
    linarith
  have hsum := sum_le_sum hpt
  have hsub : ∑ m ∈ (range (k + 1)).filter
      (fun m : ℕ => (k : ℝ) * Real.log k ≤ 2 * ((m : ℝ) - k / 2) ^ 2),
      (k.choose m : ℝ) * (exp (-(t * w)) * (exp (t * (m - k / 2)) + exp ((-t) * (m - k / 2)))) ≤
      ∑ m ∈ range (k + 1),
      (k.choose m : ℝ) * (exp (-(t * w)) * (exp (t * (m - k / 2)) + exp ((-t) * (m - k / 2)))) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun m _ _ => by positivity)
  have hfull : ∑ m ∈ range (k + 1),
      (k.choose m : ℝ) * (exp (-(t * w)) * (exp (t * (m - k / 2)) + exp ((-t) * (m - k / 2)))) =
      exp (-(t * w)) * (∑ m ∈ range (k + 1), (k.choose m : ℝ) * exp (t * (m - k / 2)) +
        ∑ m ∈ range (k + 1), (k.choose m : ℝ) * exp ((-t) * (m - k / 2))) := by
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun m _ => by ring
  have hb1 := binom_exp k t
  have hb2 := binom_exp k (-t)
  rw [neg_sq] at hb2
  have hexp : exp (-(t * w)) * (2 ^ k * exp (k * t ^ 2 / 8) + 2 ^ k * exp (k * t ^ 2 / 8)) =
      2 * 2 ^ k / k := by
    have e : -(t * w) + k * t ^ 2 / 8 = -Real.log k := by
      rw [ht]; field_simp; rw [hw2]; ring
    have : exp (-(t * w)) * (2 ^ k * exp (k * t ^ 2 / 8) + 2 ^ k * exp (k * t ^ 2 / 8)) =
        2 * 2 ^ k * exp (-(t * w) + k * t ^ 2 / 8) := by rw [exp_add]; ring
    rw [this, e, exp_neg, exp_log hk0]; field_simp
  have hfin : ∑ m ∈ (range (k + 1)).filter
      (fun m : ℕ => (k : ℝ) * Real.log k ≤ 2 * ((m : ℝ) - k / 2) ^ 2), (k.choose m : ℝ) ≤
      2 * 2 ^ k / k := by
    calc _ ≤ _ := hsum
      _ ≤ _ := hsub
      _ = _ := hfull
      _ ≤ exp (-(t * w)) * (2 ^ k * exp (k * t ^ 2 / 8) + 2 ^ k * exp (k * t ^ 2 / 8)) :=
          mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (exp_pos _).le
      _ = 2 * 2 ^ k / k := hexp
  rw [le_div_iff₀ hk0] at hfin
  linarith

theorem rare {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1 ≤ k) (hb : ∀ A, #(L A) ≤ 2)
    (Q : Finset U) (hQ : k ≤ #Q) (S : Finset C)
    (hS : ∀ u ∈ S, ∀ Y ⊆ Q, #Y = k →
      ∃ A ⊆ Y, (k : ℝ) * Real.log k ≤ 2 * ((#A : ℝ) - k / 2) ^ 2 ∧ u ∈ L A) :
    (#S : ℝ) * k ≤ 4 * 2 ^ k ∧ ((k : ℝ) - 1) * #S < 4 * 2 ^ k := by
  classical
  obtain ⟨Y, hYQ, hYc⟩ := exists_subset_card_eq hQ
  set F := Y.powerset.filter
    (fun A => (k : ℝ) * Real.log k ≤ 2 * ((#A : ℝ) - k / 2) ^ 2) with hF
  have hSF : S ⊆ F.biUnion L := by
    intro u hu
    obtain ⟨A, hAY, hc, huA⟩ := hS u hu Y hYQ hYc
    exact mem_biUnion.2 ⟨A, mem_filter.2 ⟨mem_powerset.2 hAY, hc⟩, huA⟩
  have hS2 : #S ≤ 2 * #F := by
    calc #S ≤ #(F.biUnion L) := card_le_card hSF
      _ ≤ ∑ A ∈ F, #(L A) := card_biUnion_le
      _ ≤ ∑ _A ∈ F, 2 := sum_le_sum fun A _ => hb A
      _ = 2 * #F := by rw [sum_const, smul_eq_mul, mul_comm]
  have hFc : (#F : ℝ) = ∑ m ∈ (range (k + 1)).filter
      (fun m : ℕ => (k : ℝ) * Real.log k ≤ 2 * ((m : ℝ) - k / 2) ^ 2), (k.choose m : ℝ) := by
    rw [hF, card_filter, Nat.cast_sum, sum_filter]
    have := Finset.sum_powerset_apply_card
      (fun m : ℕ => if (k : ℝ) * Real.log k ≤ 2 * ((m : ℝ) - k / 2) ^ 2 then (1 : ℝ) else 0)
      (x := Y)
    rw [hYc] at this
    push_cast
    rw [this]
    refine sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  have ht := tail_count k hk
  rw [← hFc] at ht
  have hS2' : (#S : ℝ) ≤ 2 * #F := by exact_mod_cast hS2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (#S : ℝ) * k ≤ 4 * 2 ^ k := by nlinarith
  refine ⟨h1, ?_⟩
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  nlinarith [(Nat.cast_nonneg (#S) : (0 : ℝ) ≤ #S)]
end E624R14R

namespace Erdos624

theorem rare_layer_budget {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1 ≤ k) (hb : ∀ A, #(L A) ≤ 2)
    (Q : Finset U) (hQ : k ≤ #Q) (S : Finset C)
    (hS : ∀ u ∈ S, ∀ Y ⊆ Q, #Y = k →
      ∃ A ⊆ Y, (k : ℝ) * Real.log k ≤ 2 * ((#A : ℝ) - k / 2) ^ 2 ∧ u ∈ L A) :
    (#S : ℝ) * k ≤ 4 * 2 ^ k ∧ ((k : ℝ) - 1) * #S < 4 * 2 ^ k := by
  exact E624R14R.rare L k hk hb Q hQ S hS

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1 ≤ k) (hb : ∀ A, #(L A) ≤ 2)
    (Q : Finset U) (hQ : k ≤ #Q) (S : Finset C)
    (hS : ∀ u ∈ S, ∀ Y ⊆ Q, #Y = k →
      ∃ A ⊆ Y, (k : ℝ) * Real.log k ≤ 2 * ((#A : ℝ) - k / 2) ^ 2 ∧ u ∈ L A) :
    (#S : ℝ) * k ≤ 4 * 2 ^ k ∧ ((k : ℝ) - 1) * #S < 4 * 2 ^ k :=
  Erdos624.rare_layer_budget L k hk hb Q hQ S hS

-- Prove2me | solution 1 for GeneralAgentsWorldModels.theorem1_binomial_quantile_bound
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:15:08.817947+00:00
-- url     : https://prove2.me/submissions/612d9939-5bdd-4a17-9b85-adf0ece275f7

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

set_option autoImplicit false

open Finset

open GeneralAgentsWorldModels

private lemma pmf_eval (m r : ℕ) (p : ℝ) :
    (bernsteinPolynomial ℝ m r).eval p = binPmf m p r := by
  simp [bernsteinPolynomial, binPmf]

private lemma pmf_nonneg (m r : ℕ) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ binPmf m p r := by
  unfold binPmf
  have : 0 ≤ 1 - p := by linarith
  positivity

private lemma sum_pmf (m : ℕ) (p : ℝ) : ∑ r ∈ range (m + 1), binPmf m p r = 1 := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum ℝ m)
  simpa [Polynomial.eval_finsetSum, pmf_eval] using h

private lemma mean_pmf (m : ℕ) (p : ℝ) :
    ∑ r ∈ range (m + 1), (r : ℝ) * binPmf m p r = m * p := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum_smul ℝ m)
  simpa [Polynomial.eval_finsetSum, pmf_eval, nsmul_eq_mul] using h

private lemma var_pmf (m : ℕ) (p : ℝ) :
    ∑ r ∈ range (m + 1), ((m : ℝ) * p - r) ^ 2 * binPmf m p r = m * p * (1 - p) := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.variance ℝ m)
  simpa [Polynomial.eval_finsetSum, pmf_eval, nsmul_eq_mul] using h

private lemma moment (m : ℕ) (p s : ℝ) :
    ∑ r ∈ range (m + 1), binPmf m p r * ((r : ℝ) - m * p + s) ^ 2 = m * p * (1 - p) + s ^ 2 := by
  calc ∑ r ∈ range (m + 1), binPmf m p r * ((r : ℝ) - m * p + s) ^ 2
      = ∑ r ∈ range (m + 1), (((m : ℝ) * p - r) ^ 2 * binPmf m p r
          + 2 * s * ((r : ℝ) * binPmf m p r) + (s ^ 2 - 2 * s * (m * p)) * binPmf m p r) :=
        sum_congr rfl (fun r _ => by ring)
    _ = m * p * (1 - p) + s ^ 2 := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, var_pmf, mean_pmf, sum_pmf]
        ring

private lemma upper_tail (m : ℕ) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (k : ℕ) (a : ℝ)
    (ht : 0 < (k : ℝ) - m * p) (ha : 0 ≤ a) :
    binGE m p k * ((k : ℝ) - m * p + a) ^ 2 ≤ m * p * (1 - p) + a ^ 2 := by
  rw [← moment m p a, binGE, sum_mul]
  calc ∑ r ∈ Icc k m, binPmf m p r * ((k : ℝ) - m * p + a) ^ 2
      ≤ ∑ r ∈ Icc k m, binPmf m p r * ((r : ℝ) - m * p + a) ^ 2 := by
        apply sum_le_sum
        intro r hr
        have hkr : (k : ℝ) ≤ r := by exact_mod_cast (mem_Icc.mp hr).1
        apply mul_le_mul_of_nonneg_left _ (pmf_nonneg m r p hp₀ hp₁)
        apply pow_le_pow_left₀ (by linarith) (by linarith)
    _ ≤ ∑ r ∈ range (m + 1), binPmf m p r * ((r : ℝ) - m * p + a) ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro r hr
          simp only [mem_Icc] at hr
          simp only [mem_range]
          omega
        · intro r _ _
          exact mul_nonneg (pmf_nonneg m r p hp₀ hp₁) (sq_nonneg _)

private lemma lower_tail (m : ℕ) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (k : ℕ) (a : ℝ)
    (ht : 0 < m * p - (k : ℝ)) (ha : 0 ≤ a) :
    binLE m p k * (m * p - (k : ℝ) + a) ^ 2 ≤ m * p * (1 - p) + (-a) ^ 2 := by
  have hkm : k ≤ m := by
    have h1 : (m : ℝ) * p ≤ m := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    have : (k : ℝ) < m := by linarith
    exact_mod_cast this.le
  rw [← moment m p (-a), binLE, sum_mul]
  calc ∑ r ∈ range (k + 1), binPmf m p r * (m * p - (k : ℝ) + a) ^ 2
      ≤ ∑ r ∈ range (k + 1), binPmf m p r * ((r : ℝ) - m * p + -a) ^ 2 := by
        apply sum_le_sum
        intro r hr
        have hkr : (r : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hr)
        apply mul_le_mul_of_nonneg_left _ (pmf_nonneg m r p hp₀ hp₁)
        have e : ((r : ℝ) - m * p + -a) ^ 2 = (m * p - r + a) ^ 2 := by ring
        rw [e]
        apply pow_le_pow_left₀ (by linarith) (by linarith)
    _ ≤ ∑ r ∈ range (m + 1), binPmf m p r * ((r : ℝ) - m * p + -a) ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro r hr
          simp only [mem_range] at hr ⊢
          omega
        · intro r _ _
          exact mul_nonneg (pmf_nonneg m r p hp₀ hp₁) (sq_nonneg _)

private lemma alg (B t S a δ : ℝ) (hδ₁ : δ < 1) (hc : (1 - δ) / (2 - δ) ≤ B) (ht : 0 < t)
    (hS : 0 ≤ S) (hat : a * t = S) (hB : B * (t + a) ^ 2 ≤ S + a ^ 2) :
    t ^ 2 ≤ S / (1 - δ) := by
  have h2δ : 0 < 2 - δ := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  have hc' : (1 - δ) / (2 - δ) * (t + a) ^ 2 ≤ S + a ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) hB
  rw [div_mul_eq_mul_div, div_le_iff₀ h2δ] at hc'
  have h3 : (1 - δ) * (t ^ 2 + S) ^ 2 ≤ S * (t ^ 2 + S) * (2 - δ) := by
    have := mul_le_mul_of_nonneg_right hc' (sq_nonneg t)
    calc (1 - δ) * (t ^ 2 + S) ^ 2 = (1 - δ) * (t + a) ^ 2 * t ^ 2 := by rw [← hat]; ring
      _ ≤ (S + a ^ 2) * (2 - δ) * t ^ 2 := this
      _ = S * (t ^ 2 + S) * (2 - δ) := by rw [← hat]; ring
  have hpos : 0 < t ^ 2 + S := by positivity
  have h4 : (1 - δ) * (t ^ 2 + S) ≤ S * (2 - δ) := by
    have : (1 - δ) * (t ^ 2 + S) * (t ^ 2 + S) ≤ S * (2 - δ) * (t ^ 2 + S) := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos
  rw [le_div_iff₀ h1δ]
  nlinarith

theorem solution (m : ℕ) (p δ : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (k : ℕ)
    (hle : (1 - δ) / (2 - δ) ≤ binLE m p k) (hge : (1 - δ) / (2 - δ) ≤ binGE m p k) :
    |(k : ℝ) - m * p| ≤ Real.sqrt (m * p * (1 - p) / (1 - δ)) := by
  apply Real.abs_le_sqrt
  have hS : 0 ≤ (m : ℝ) * p * (1 - p) := by
    have : 0 ≤ 1 - p := by linarith
    positivity
  rcases lt_trichotomy ((k : ℝ) - m * p) 0 with h | h | h
  · -- lower tail
    set t := (m : ℝ) * p - k with ht_def
    have ht : 0 < t := by linarith
    have e : ((k : ℝ) - m * p) ^ 2 = t ^ 2 := by rw [ht_def]; ring
    rw [e]
    set S := (m : ℝ) * p * (1 - p)
    have hat : S / t * t = S := div_mul_cancel₀ S ht.ne'
    have hB := lower_tail m p hp₀ hp₁ k (S / t) ht (div_nonneg hS ht.le)
    rw [neg_sq] at hB
    exact alg _ t S (S / t) δ hδ₁ hle ht hS hat hB
  · rw [h]
    have : (0 : ℝ) < 1 - δ := by linarith
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · -- upper tail
    set t := (k : ℝ) - m * p with ht_def
    set S := (m : ℝ) * p * (1 - p)
    have hat : S / t * t = S := div_mul_cancel₀ S h.ne'
    have hB := upper_tail m p hp₀ hp₁ k (S / t) h (div_nonneg hS h.le)
    exact alg _ t S (S / t) δ hδ₁ hge h hS hat hB

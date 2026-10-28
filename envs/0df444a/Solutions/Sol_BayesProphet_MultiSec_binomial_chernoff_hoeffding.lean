-- Prove2me | solution 1 for BayesProphet.MultiSec.binomial_chernoff_hoeffding
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T05:49:39.845184+00:00
-- url     : https://prove2.me/submissions/d10ccfbe-415c-4145-8c21-680dd8f71f8c

import Mathlib

namespace Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace BayesProphet.MultiSec

noncomputable def binomialWeight (t : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (t.choose k : ℝ) * p ^ k * (1 - p) ^ (t - k)

lemma weight_nonneg (t : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ binomialWeight t p k := by
  unfold binomialWeight
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

lemma weight_sum_one (t : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (t + 1), binomialWeight t p k = 1 := by
  have h := add_pow p (1 - p) t
  have hp : p + (1 - p) = (1 : ℝ) := by ring
  rw [hp, one_pow] at h
  calc
    ∑ k ∈ Finset.range (t + 1), binomialWeight t p k
      = ∑ k ∈ Finset.range (t + 1), p ^ k * (1 - p) ^ (t - k) * (t.choose k : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        unfold binomialWeight
        ring
    _ = 1 := h.symm

lemma exp_dev (s p : ℝ) (t k : ℕ) :
    Real.exp (s * ((k : ℝ) - t * p)) =
      Real.exp (-(s * t * p)) * (Real.exp s) ^ k := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

lemma centred_mgf_factor (t : ℕ) (p s : ℝ) :
    (∑ k ∈ Finset.range (t + 1),
      binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p))) =
    ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))) ^ t := by
  have hsum : (∑ k ∈ Finset.range (t + 1),
      binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p))) =
    (∑ k ∈ Finset.range (t + 1),
      (t.choose k : ℝ) * (p * Real.exp s) ^ k * (1 - p) ^ (t - k)) *
        Real.exp (-(s * t * p)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [exp_dev]
    unfold binomialWeight
    ring
  rw [hsum]
  have hbin : (p * Real.exp s + (1 - p)) ^ t =
      ∑ k ∈ Finset.range (t + 1),
        (t.choose k : ℝ) * (p * Real.exp s) ^ k * (1 - p) ^ (t - k) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [← hbin]
  have hexp : Real.exp (-(s * t * p)) = (Real.exp (-(s * p))) ^ t := by
    rw [show -(s * t * p) = (t : ℝ) * (-(s * p)) by ring, Real.exp_nat_mul]
  rw [hexp, ← mul_pow]
  congr 1
  rw [add_mul]
  rw [mul_assoc]
  rw [← Real.exp_add]
  have harg : s + -(s * p) = s * (1 - p) := by ring
  rw [harg]
  ring

lemma bernoulli_mgf_le (p s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p)) ≤ Real.exp (s ^ 2 / 8) := by
  let q : unitInterval := ⟨p, hp0, hp1⟩
  let μ : Measure Bool := ProbabilityTheory.bernoulliMeasure (true : Bool) false q
  let X : Bool → ℝ := fun b => if b then 1 else 0
  have hmean : ∫ x, X x ∂μ = p := by
    simp [μ, X, q, ProbabilityTheory.integral_bernoulliMeasure]
  have hsub : HasSubgaussianMGF (fun b => X b - ∫ x, X x ∂μ) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    apply ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    · fun_prop
    · filter_upwards with x
      cases x <;> simp [X]
  have hle := hsub.mgf_le s
  have hmgf : mgf (fun b => X b - ∫ x, X x ∂μ) μ s =
      (1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p)) := by
    rw [mgf, hmean, ProbabilityTheory.integral_bernoulliMeasure]
    simp only [X, q, Bool.false_eq_true, ↓reduceIte]
    ring_nf
  rw [hmgf] at hle
  norm_num at hle
  have hExp : (1 / 4 * s ^ 2 / 2) = s ^ 2 / 8 := by ring
  rw [hExp] at hle
  simpa [neg_mul] using hle

lemma factor_nonneg (p s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ (1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p)) := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  exact add_nonneg (mul_nonneg hq (Real.exp_nonneg _)) (mul_nonneg hp0 (Real.exp_nonneg _))

lemma exp_tail_factor (s p ε : ℝ) (t k : ℕ) (w : ℝ) :
    Real.exp (-(s * (t : ℝ) * ε)) * (w * Real.exp (s * ((k : ℝ) - t * p))) =
      w * Real.exp (s * ((k : ℝ) - t * p - (t : ℝ) * ε)) := by
  calc
    Real.exp (-(s * (t : ℝ) * ε)) * (w * Real.exp (s * ((k : ℝ) - t * p)))
        = w * (Real.exp (-(s * (t : ℝ) * ε)) *
            Real.exp (s * ((k : ℝ) - t * p))) := by ring
    _ = w * Real.exp (-(s * (t : ℝ) * ε) + s * ((k : ℝ) - t * p)) := by
      rw [← Real.exp_add]
    _ = w * Real.exp (s * ((k : ℝ) - t * p - (t : ℝ) * ε)) := by
      congr 2
      ring

lemma upper_tail_le_exp (t : ℕ) {p ε s : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s) :
    (∑ k ∈ (Finset.range (t + 1)).filter
        (fun k : ℕ => t * ε ≤ (k : ℝ) - t * p), binomialWeight t p k) ≤
      Real.exp (-(s * (t : ℝ) * ε) + (t : ℝ) * s ^ 2 / 8) := by
  let F := (Finset.range (t + 1)).filter (fun k : ℕ => t * ε ≤ (k : ℝ) - t * p)
  have h1 : (∑ k ∈ F, binomialWeight t p k) ≤
      ∑ k ∈ F, binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p - (t : ℝ) * ε)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hevent : t * ε ≤ (k : ℝ) - t * p := (Finset.mem_filter.mp hk).2
    have harg : 0 ≤ s * ((k : ℝ) - t * p - (t : ℝ) * ε) := by
      apply mul_nonneg hs
      linarith
    calc
      binomialWeight t p k = binomialWeight t p k * 1 := by ring
      _ ≤ binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p - (t : ℝ) * ε)) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp harg) (weight_nonneg t hp0 hp1 k)
  have h2 : (∑ k ∈ F, binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p - (t : ℝ) * ε))) =
      Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ F, binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact (exp_tail_factor s p ε t k (binomialWeight t p k)).symm
  have h3 : Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ F, binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p)) ≤
      Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ Finset.range (t + 1), binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p)) := by
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro k hk hkF
        exact mul_nonneg (weight_nonneg t hp0 hp1 k) (Real.exp_nonneg _)
    · exact Real.exp_nonneg _
  have h4 : (∑ k ∈ Finset.range (t + 1),
        binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p))) =
      ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))) ^ t :=
    centred_mgf_factor t p s
  have h5 : ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))) ^ t ≤
      Real.exp ((t : ℝ) * s ^ 2 / 8) := by
    have hpow := pow_le_pow_left₀ (factor_nonneg p s hp0 hp1)
      (bernoulli_mgf_le p s hp0 hp1) t
    calc
      ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))) ^ t
          ≤ (Real.exp (s ^ 2 / 8)) ^ t := hpow
      _ = Real.exp ((t : ℝ) * s ^ 2 / 8) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    (∑ k ∈ F, binomialWeight t p k) ≤
        Real.exp (-(s * (t : ℝ) * ε)) *
          ∑ k ∈ F, binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p)) := h1.trans h2.le
    _ ≤ Real.exp (-(s * (t : ℝ) * ε)) *
          ∑ k ∈ Finset.range (t + 1), binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p)) := h3
    _ = Real.exp (-(s * (t : ℝ) * ε)) *
          ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))) ^ t := by
      rw [h4]
    _ ≤ Real.exp (-(s * (t : ℝ) * ε)) * Real.exp ((t : ℝ) * s ^ 2 / 8) := by
      apply mul_le_mul_of_nonneg_left h5
      exact Real.exp_nonneg _
    _ = Real.exp (-(s * (t : ℝ) * ε) + (t : ℝ) * s ^ 2 / 8) := by
      rw [← Real.exp_add]

lemma lower_tail_le_exp (t : ℕ) {p ε s : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s) :
    (∑ k ∈ (Finset.range (t + 1)).filter
        (fun k : ℕ => (k : ℝ) - t * p ≤ -(t * ε)), binomialWeight t p k) ≤
      Real.exp (-(s * (t : ℝ) * ε) + (t : ℝ) * s ^ 2 / 8) := by
  let F := (Finset.range (t + 1)).filter (fun k : ℕ => (k : ℝ) - t * p ≤ -(t * ε))
  have h1 : (∑ k ∈ F, binomialWeight t p k) ≤
      ∑ k ∈ F, binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ) - (t : ℝ) * ε)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hevent : (k : ℝ) - t * p ≤ -(t * ε) := (Finset.mem_filter.mp hk).2
    have harg : 0 ≤ s * (t * p - (k : ℝ) - (t : ℝ) * ε) := by
      apply mul_nonneg hs
      linarith
    calc
      binomialWeight t p k = binomialWeight t p k * 1 := by ring
      _ ≤ binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ) - (t : ℝ) * ε)) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp harg) (weight_nonneg t hp0 hp1 k)
  have h2 : (∑ k ∈ F, binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ) - (t : ℝ) * ε))) =
      Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ F, binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ) - (t : ℝ) * ε))
          = binomialWeight t p k * (Real.exp (-(s * (t : ℝ) * ε)) *
              Real.exp (s * (t * p - (k : ℝ)))) := by
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (-(s * (t : ℝ) * ε)) *
            (binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ)))) := by ring
  have h3 : Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ F, binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ))) ≤
      Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ Finset.range (t + 1), binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ))) := by
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro k hk hkF
        exact mul_nonneg (weight_nonneg t hp0 hp1 k) (Real.exp_nonneg _)
    · exact Real.exp_nonneg _
  have hfull : (∑ k ∈ Finset.range (t + 1),
        binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ)))) =
      ((1 - p) * Real.exp (s * p) + p * Real.exp (-(s * (1 - p)))) ^ t := by
    calc
      (∑ k ∈ Finset.range (t + 1),
          binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ)))) =
          ∑ k ∈ Finset.range (t + 1),
            binomialWeight t p k * Real.exp ((-s) * ((k : ℝ) - t * p)) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        ring
      _ = ((1 - p) * Real.exp (-((-s) * p)) + p * Real.exp ((-s) * (1 - p))) ^ t :=
        centred_mgf_factor t p (-s)
      _ = ((1 - p) * Real.exp (s * p) + p * Real.exp (-(s * (1 - p)))) ^ t := by
        congr 1
        ring_nf
  have h5 : ((1 - p) * Real.exp (s * p) + p * Real.exp (-(s * (1 - p)))) ^ t ≤
      Real.exp ((t : ℝ) * s ^ 2 / 8) := by
    have hpow := pow_le_pow_left₀ (factor_nonneg p (-s) hp0 hp1)
      (bernoulli_mgf_le p (-s) hp0 hp1) t
    calc
      ((1 - p) * Real.exp (s * p) + p * Real.exp (-(s * (1 - p)))) ^ t
          = ((1 - p) * Real.exp (-((-s) * p)) + p * Real.exp ((-s) * (1 - p))) ^ t := by
        congr 1
        ring_nf
      _ ≤ (Real.exp ((-s) ^ 2 / 8)) ^ t := hpow
      _ = Real.exp ((t : ℝ) * s ^ 2 / 8) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    (∑ k ∈ F, binomialWeight t p k) ≤
        Real.exp (-(s * (t : ℝ) * ε)) *
          ∑ k ∈ F, binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ))) := h1.trans h2.le
    _ ≤ Real.exp (-(s * (t : ℝ) * ε)) *
          ∑ k ∈ Finset.range (t + 1), binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ))) := h3
    _ = Real.exp (-(s * (t : ℝ) * ε)) *
          ((1 - p) * Real.exp (s * p) + p * Real.exp (-(s * (1 - p)))) ^ t := by
      rw [hfull]
    _ ≤ Real.exp (-(s * (t : ℝ) * ε)) * Real.exp ((t : ℝ) * s ^ 2 / 8) := by
      apply mul_le_mul_of_nonneg_left h5
      exact Real.exp_nonneg _
    _ = Real.exp (-(s * (t : ℝ) * ε) + (t : ℝ) * s ^ 2 / 8) := by
      rw [← Real.exp_add]

theorem binomial_chernoff_hoeffding (t : ℕ) (α ε : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hε : 0 ≤ ε) :
    ∑ k ∈ (Finset.range (t + 1)).filter (fun k : ℕ => (k : ℝ) - t * α ≤ -(t * ε)),
        (t.choose k : ℝ) * α ^ k * (1 - α) ^ (t - k) ≤ Real.exp (-2 * ε ^ 2 * t) ∧
    ∑ k ∈ (Finset.range (t + 1)).filter (fun k : ℕ => t * ε ≤ (k : ℝ) - t * α),
        (t.choose k : ℝ) * α ^ k * (1 - α) ^ (t - k) ≤ Real.exp (-2 * ε ^ 2 * t) := by
  have hs : 0 ≤ 4 * ε := by positivity
  constructor
  · have h := lower_tail_le_exp (t := t) (p := α) (ε := ε) (s := 4 * ε) hα₀ hα₁ hs
    have harg : -((4 * ε) * (t : ℝ) * ε) + (t : ℝ) * (4 * ε) ^ 2 / 8 =
        -2 * ε ^ 2 * (t : ℝ) := by ring
    simpa [binomialWeight, harg] using h
  · have h := upper_tail_le_exp (t := t) (p := α) (ε := ε) (s := 4 * ε) hα₀ hα₁ hs
    have harg : -((4 * ε) * (t : ℝ) * ε) + (t : ℝ) * (4 * ε) ^ 2 / 8 =
        -2 * ε ^ 2 * (t : ℝ) := by ring
    simpa [binomialWeight, harg] using h

end BayesProphet.MultiSec

end Prove2SwarmSubmission

theorem solution (t : ℕ) (α ε : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hε : 0 ≤ ε) :
    ∑ k ∈ (Finset.range (t + 1)).filter (fun k : ℕ => (k : ℝ) - t * α ≤ -(t * ε)),
        (t.choose k : ℝ) * α ^ k * (1 - α) ^ (t - k) ≤ Real.exp (-2 * ε ^ 2 * t) ∧
    ∑ k ∈ (Finset.range (t + 1)).filter (fun k : ℕ => t * ε ≤ (k : ℝ) - t * α),
        (t.choose k : ℝ) * α ^ k * (1 - α) ^ (t - k) ≤ Real.exp (-2 * ε ^ 2 * t) := by
  exact Prove2SwarmSubmission.BayesProphet.MultiSec.binomial_chernoff_hoeffding t α ε hα₀ hα₁ hε

-- Prove2me | solution 1 for FournierGuillin.Conc.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:36:05.358712+00:00
-- url     : https://prove2.me/submissions/e1e9c5e3-1bb4-4b86-bcda-1fcd53c14fe6

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_FournierGuillin_Moment_Setting
import Definitions.Def_FournierGuillin_Conc_Setting
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal

namespace Aux_FGLemma11

lemma fact_bound (N k : ℕ) :
    (((N + k).factorial : ℕ) : ℝ) ≤ (N.factorial : ℝ) * ((N : ℝ) + k) ^ k := by
  have h1 := Nat.factorial_mul_descFactorial (show k ≤ N + k by omega)
  rw [Nat.add_sub_cancel] at h1
  have h2 := Nat.descFactorial_le_pow (N + k) k
  have : (N + k).factorial ≤ N.factorial * (N + k) ^ k := by
    rw [← h1]; exact Nat.mul_le_mul_left _ h2
  exact_mod_cast this

lemma stirling_bound (N : ℕ) (hN : 1 ≤ N) :
    (N.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt N * ((N : ℝ) ^ N / Real.exp N) := by
  have hanti : Stirling.stirlingSeq N ≤ Stirling.stirlingSeq 1 := by
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le (N - 1))
    simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add, Nat.sub_add_cancel hN] at this
    exact this
  rw [Stirling.stirlingSeq_one] at hanti
  unfold Stirling.stirlingSeq at hanti
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < Real.sqrt (2 * N) * ((N : ℝ) / Real.exp 1) ^ N := by positivity
  rw [div_le_iff₀ hpos] at hanti
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  calc (N.factorial : ℝ)
      ≤ Real.exp 1 / Real.sqrt 2 * (Real.sqrt (2 * N) * ((N : ℝ) / Real.exp 1) ^ N) := hanti
    _ = Real.exp 1 * Real.sqrt N * ((N : ℝ) ^ N / Real.exp N) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), div_pow, Real.exp_one_pow]
      field_simp

lemma exp_bound (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ Nat.sqrt N) :
    ((N : ℝ) + k) ^ k ≤ Real.exp 1 * (N : ℝ) ^ k := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk2 : ((k : ℝ)) ^ 2 ≤ N := by
    have : k ^ 2 ≤ N := (Nat.pow_le_pow_left hk 2).trans (Nat.sqrt_le' N)
    exact_mod_cast this
  have h1 : (N : ℝ) + k ≤ N * Real.exp (k / N) := by
    have e : (N : ℝ) + k = N * (k / N + 1) := by
      rw [mul_add, mul_one, mul_div_cancel₀ (k : ℝ) hN0.ne']; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hN0.le
  have h2 : ((N : ℝ) + k) ^ k ≤ (N * Real.exp (k / N)) ^ k :=
    pow_le_pow_left₀ (by positivity) h1 k
  rw [mul_pow, ← Real.exp_nat_mul] at h2
  have h3 : Real.exp (k * (k / N)) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.2
    rw [mul_div_assoc', div_le_one hN0]
    nlinarith
  calc ((N : ℝ) + k) ^ k ≤ (N : ℝ) ^ k * Real.exp (k * (k / N)) := h2
    _ ≤ (N : ℝ) ^ k * Real.exp 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = Real.exp 1 * (N : ℝ) ^ k := by ring

end Aux_FGLemma11

open Aux_FGLemma11 in
theorem solution (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ Nat.sqrt N) :
    ENNReal.ofReal (Real.exp (-2) / Real.sqrt 2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      ProbabilityTheory.poissonMeasure (N : ℝ≥0) {N + k} := by
  rw [ProbabilityTheory.poissonMeasure_singleton]
  apply ENNReal.ofReal_le_ofReal
  simp only [NNReal.coe_natCast]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hfpos : (0 : ℝ) < ((N + k).factorial : ℝ) := by positivity
  rw [Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow]
  have hs2 : 1 ≤ Real.sqrt 2 := by
    have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have := Real.sqrt_nonneg 2
    nlinarith
  have step1 : Real.exp (-2) / Real.sqrt 2 * (Real.sqrt N)⁻¹ ≤
      Real.exp (-2) * (Real.sqrt N)⁻¹ :=
    mul_le_mul_of_nonneg_right (div_le_self (by positivity) hs2) (by positivity)
  refine step1.trans ?_
  rw [le_div_iff₀ hfpos]
  have hF : (((N + k).factorial : ℕ) : ℝ) ≤
      Real.exp 1 * Real.sqrt N * ((N : ℝ) ^ N / Real.exp N) * (Real.exp 1 * (N : ℝ) ^ k) :=
    (fact_bound N k).trans (mul_le_mul (stirling_bound N hN) (exp_bound N k hN hk)
      (by positivity) (by positivity))
  have e2 : Real.exp (-2) * Real.exp 1 * Real.exp 1 = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have hs : (Real.sqrt N)⁻¹ * Real.sqrt N = 1 := inv_mul_cancel₀ hsN.ne'
  calc Real.exp (-2) * (Real.sqrt N)⁻¹ * (((N + k).factorial : ℕ) : ℝ)
      ≤ Real.exp (-2) * (Real.sqrt N)⁻¹ *
          (Real.exp 1 * Real.sqrt N * ((N : ℝ) ^ N / Real.exp N) * (Real.exp 1 * (N : ℝ) ^ k)) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
    _ = (Real.exp (-2) * Real.exp 1 * Real.exp 1) * ((Real.sqrt N)⁻¹ * Real.sqrt N) *
          ((N : ℝ) ^ N * (N : ℝ) ^ k * (Real.exp N)⁻¹) := by ring
    _ = Real.exp (-(N : ℝ)) * (N : ℝ) ^ (N + k) := by
      rw [e2, hs, Real.exp_neg, pow_add]; ring

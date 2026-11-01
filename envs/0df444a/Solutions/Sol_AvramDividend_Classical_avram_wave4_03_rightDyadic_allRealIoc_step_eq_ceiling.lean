-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:50:57.305122+00:00
-- url     : https://prove2.me/submissions/74bf437b-cdd0-495a-b0af-fa023285d2b8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_realIoc_step_eq_ceiling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Whole-real-time dyadic kernel equals the complete Ioc-cell step sum. -/
theorem solution
    (T : ℝ≥0) (hT : 0 < T) (s : ℝ)
    (n : ℕ) (a : ℕ → ℝ≥0∞) :
    (∑ i ∈ Finset.range (2 ^ n),
      if s ∈ Ioc
        (((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ)
        (((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ)
      then a (i + 1) else 0) =
    if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      a (Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n))
    else 0 := by
  classical
  by_cases hs : s ∈ Ioc (0 : ℝ) (T : ℝ)
  · have hTp : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    have hreal := avram_wave4_03_rightDyadic_realIoc_step_eq_ceiling
      (T : ℝ) s hTp hs.1 hs.2 (2 ^ n) hp a
    have hdiv (i : ℕ) :
        (((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ) =
        (i : ℝ) * (T : ℝ) / (((2 : ℕ) ^ n) : ℝ) := by
      push_cast
      ring
    have hdiv' (i : ℕ) :
        (((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ) =
        ((i + 1 : ℕ) : ℝ) * (T : ℝ) / (((2 : ℕ) ^ n) : ℝ) := by
      push_cast
      ring
    have hrhs :
        (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n) =
        (s / (T : ℝ)) * (((2 : ℕ) ^ n) : ℝ) := by
      push_cast
      simp only [Real.coe_toNNReal s hs.1.le]
    have hmesh :
        (∑ i ∈ Finset.range (2 ^ n),
          if s ∈ Ioc
            (((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ)
            (((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ)
          then a (i + 1) else 0) =
        a (Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)) := by
      simpa only [hdiv, hdiv', hrhs, Nat.cast_pow, Nat.cast_ofNat] using hreal
    simpa only [if_pos hs] using hmesh
  · simp only [if_neg hs]
    apply Finset.sum_eq_zero
    intro i hi
    have hip : i + 1 ≤ 2 ^ n := by
      have hii : i < 2 ^ n := Finset.mem_range.mp hi
      omega
    have hpow : 0 < (2 : ℝ≥0) ^ n := pow_pos (by norm_num) _
    have hratio :
        (((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ≤ 1 := by
      apply (div_le_one hpow).2
      exact_mod_cast hip
    have hupper :
        (((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ) ≤
        (T : ℝ) := by
      have ht := mul_le_mul_of_nonneg_right hratio (by positivity)
      have hsimple :
          ((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) ≤ T := by
        simpa using ht
      exact_mod_cast hsimple
    have hnot :
        s ∉ Ioc
          (((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ)
          (((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ) := by
      intro hcell
      apply hs
      refine ⟨?_, le_trans hcell.2 hupper⟩
      have hnonneg : (0 : ℝ) ≤
          (((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ) := by
        positivity
      exact lt_of_le_of_lt hnonneg hcell.1
    simp only [if_neg hnot]

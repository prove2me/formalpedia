-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_rightDyadic_nnrealIoc_step_eq_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:41:15.134195+00:00
-- url     : https://prove2.me/submissions/0db33f44-eed9-43b6-924f-5514879ba747

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_realIoc_step_eq_ceiling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The original NNReal dyadic clock has exactly the real Ioc half-open cells. -/
theorem solution (T s : ℝ≥0) (hT : 0 < T) (hs : 0 < s) (hsT : s ≤ T)
    (n : ℕ) (a : ℕ → ℝ≥0∞) :
    (∑ i ∈ Finset.range (2 ^ n),
      if (s : ℝ) ∈ Ioc
        (((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ)
        (((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ)
      then a (i + 1) else 0) =
    a (Nat.ceil (((s / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)) := by
  classical
  have hTp : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hsp : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hsTp : (s : ℝ) ≤ (T : ℝ) := by exact_mod_cast hsT
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have hfrom := avram_wave4_03_rightDyadic_realIoc_step_eq_ceiling
    (T : ℝ) (s : ℝ) hTp hsp hsTp (2 ^ n) hp a
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
      (((s / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n) =
      ((s : ℝ) / (T : ℝ)) * (((2 : ℕ) ^ n) : ℝ) := by
    push_cast
    ring
  simpa only [hdiv, hdiv', hrhs, Nat.cast_pow, Nat.cast_ofNat] using hfrom

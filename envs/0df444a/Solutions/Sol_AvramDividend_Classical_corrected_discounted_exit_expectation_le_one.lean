-- Prove2me | solution 1 for AvramDividend.Classical.corrected_discounted_exit_expectation_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:24:01.02655+00:00
-- url     : https://prove2.me/submissions/476413f6-49a9-4067-9ab1-526b3a6dda34

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 ≤ q) (τ : Ω → ℝ≥0∞) :
    (∫⁻ ω, (if τ ω = ⊤ then (0 : ℝ≥0∞) else
      ENNReal.ofReal (Real.exp (-(q * (τ ω).toReal)))) ∂P) ≤ 1 := by
  have hpayoff (t : ℝ≥0∞) :
      (if t = ⊤ then (0 : ℝ≥0∞) else
        ENNReal.ofReal (Real.exp (-(q * t.toReal)))) ≤ 1 := by
    by_cases ht : t = ⊤
    · simp [ht]
    · simp only [if_neg ht]
      have hmul : 0 ≤ q * t.toReal :=
        mul_nonneg hq ENNReal.toReal_nonneg
      have hexp : Real.exp (-(q * t.toReal)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr hmul)
      calc
        ENNReal.ofReal (Real.exp (-(q * t.toReal))) ≤
          ENNReal.ofReal (1 : ℝ) :=
            ENNReal.ofReal_le_ofReal hexp
        _ = 1 := by norm_num
  calc
    (∫⁻ ω, (if τ ω = ⊤ then (0 : ℝ≥0∞) else
      ENNReal.ofReal (Real.exp (-(q * (τ ω).toReal)))) ∂P) ≤
      ∫⁻ _ω : Ω, (1 : ℝ≥0∞) ∂P := by
        apply lintegral_mono
        intro ω
        exact hpayoff (τ ω)
    _ = 1 := by simp

-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_clock_stopped_kernel_indicator_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:09:51.760625+00:00
-- url     : https://prove2.me/submissions/3f6ca4c0-906b-4183-8f75-26e417c7e62c

import Mathlib.Algebra.Notation.Indicator
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} (T : ℝ≥0) (τ : Ω → ℝ≥0∞)
    (hτT : ∀ ω, τ ω ≤ (T : ℝ≥0∞))
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : S = {p | p.1.1 ≤ T})
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) :
    S.indicator (fun p => if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0) =
      (fun p => if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0) := by
  classical
  funext p
  by_cases hp : p ∈ S
  · simp only [Set.indicator_of_mem hp]
  · have hn : ¬ ((p.1.1 : ℝ≥0∞) ≤ τ p.1.2) := by
      intro hstop
      have hT : (p.1.1 : ℝ≥0∞) ≤ (T : ℝ≥0∞) :=
        hstop.trans (hτT p.1.2)
      have hreal : p.1.1 ≤ T := ENNReal.coe_le_coe.mp hT
      apply hp
      simpa only [hS, Set.mem_setOf_eq] using hreal
    simp only [Set.indicator_of_notMem hp, if_neg hn]

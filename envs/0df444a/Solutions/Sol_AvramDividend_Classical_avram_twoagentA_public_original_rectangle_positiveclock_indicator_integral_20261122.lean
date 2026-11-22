-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_rectangle_positiveclock_indicator_integral_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:23:24.348094+00:00
-- url     : https://prove2.me/submissions/5e1bb39b-1d3b-44f4-87b0-4a93e82a633a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (μ : Measure (ℝ≥0 × ℝ)) :
    (∫ p : ℝ≥0 × ℝ,
      (if p.1 ≤ T then
        (if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 ∈ B then p.2 else 0)
       else 0) ∂μ) =
    (∫ p in Ioc 0 T ×ˢ B, p.2 ∂μ) := by
  classical
  have hEq :
      (fun p : ℝ≥0 × ℝ =>
        if p.1 ≤ T then
          (if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 ∈ B then p.2 else 0)
        else 0) =
        (Ioc (0 : ℝ≥0) T ×ˢ B).indicator (fun p => p.2) := by
    funext p
    by_cases ht : p.1 ≤ T
    · simp [ht, Set.indicator, Set.mem_prod, Set.mem_Ioc]
    · simp [ht, Set.indicator, Set.mem_prod, Set.mem_Ioc]
  rw [hEq, MeasureTheory.integral_indicator
    (measurableSet_Ioc.prod hB)]

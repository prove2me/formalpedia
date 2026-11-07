-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_halfopen_marked_exponential_factor_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:32:17.627779+00:00
-- url     : https://prove2.me/submissions/25b68526-c59c-47b9-9500-659cb03ca85d

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_halfopen_marked_lintegral_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite half-open marked Laplace integrals have multiplicative weights. -/
theorem solution
    (μ : Measure (ℝ≥0 × ℝ))
    (g : ℝ≥0 × ℝ → ℝ≥0∞) (hg : Measurable g)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hLeft : (∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ s then g p else 0 ∂μ) ≠ ∞)
    (hRight : (∫⁻ p : ℝ≥0 × ℝ, if s < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ) ≠ ∞) :
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ).toReal)) =
      Real.exp (-((∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ s then g p else 0 ∂μ).toReal)) *
      Real.exp (-((∫⁻ p : ℝ≥0 × ℝ, if s < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ).toReal)) := by
  rw [avram_bv_jump8_halfopen_marked_lintegral_split μ g hg s t hst]
  rw [ENNReal.toReal_add hLeft hRight]
  rw [neg_add, Real.exp_add]

-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_masked_discounted_mark_rate_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:28:59.830294+00:00
-- url     : https://prove2.me/submissions/fd890a6c-2a3c-4351-9a4e-d4efbae28cb2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Discounting and the original stopped closed cap preserve the mark-rate bound. -/
theorem solution
    (C τ : ℝ≥0∞) (U : ℝ≥0 → ℝ) (ψ : ℝ → ℝ)
    (B q : ℝ) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (hψ : ∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b ≤ C → |ψ b| ≤ B)
    (t : ℝ≥0) :
    |if (t : ℝ≥0∞) < τ ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then
         Real.exp (-(q * (t : ℝ))) * ψ (U t)
       else 0| ≤ B := by
  by_cases h : (t : ℝ≥0∞) < τ ∧
       0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
  · have hqt : 0 ≤ q * (t : ℝ) := mul_nonneg hq (NNReal.coe_nonneg t)
    have he0 : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
      (Real.exp_pos _).le
    have he1 : Real.exp (-(q * (t : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqt)
    have hb : |ψ (U t)| ≤ B := hψ _ h.2.1 h.2.2
    have hmul : Real.exp (-(q * (t : ℝ))) * |ψ (U t)| ≤ B := by
      calc
        Real.exp (-(q * (t : ℝ))) * |ψ (U t)| ≤
            1 * |ψ (U t)| := mul_le_mul_of_nonneg_right he1 (abs_nonneg _)
        _ = |ψ (U t)| := one_mul _
        _ ≤ B := hb
    simpa only [if_pos h, abs_mul, abs_of_nonneg he0] using hmul
  · simpa only [if_neg h, abs_zero] using hB

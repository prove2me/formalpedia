-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_truegrid_zero_clock_payment_sum_is_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:34:06.172214+00:00
-- url     : https://prove2.me/submissions/d3b74542-2b9a-4904-b24a-5608a7fb2a6e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_truegrid_at_zero_clock_is_initial_singleton
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} (n k : ℕ) (ρ : Ω → ℝ≥0)
    (ω : Ω) (hzero : ρ ω = 0)
    (f : ℝ≥0 → ℝ) :
    (∑ t ∈ (((Finset.range (k + 1)).image
      (fun i : ℕ => min
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
        (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)), f t)
      = f 0 := by 
  rw [avram_pj_workerC_truegrid_at_zero_clock_is_initial_singleton
    n k ρ ω hzero]
  simp

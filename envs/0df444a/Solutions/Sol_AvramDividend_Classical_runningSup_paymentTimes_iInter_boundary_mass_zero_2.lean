-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_paymentTimes_iInter_boundary_mass_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:49:01.450222+00:00
-- url     : https://prove2.me/submissions/a4ab09b6-ae86-47db-b7e2-75dba6d706c4

import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_paymentTimes_iInter_diff_iInf_subset_terminal
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_nonnegative_atoms

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) :
    (dividendMeasure (runningSup X) ω)
      ((⋂ n, paymentTimes (σ n)) \
        paymentTimes (⨅ n, σ n)) = 0 := by
  refine measure_mono_null (fun t ht => ?_)
    (AvramDividend.Classical.runningSup_dividendMeasure_no_nonnegative_atoms X ω
      (⨅ n, σ n).toReal ENNReal.toReal_nonneg)
  have h0 : 0 ≤ t := (mem_iInter.mp ht.1 0).1
  have h := AvramDividend.Classical.paymentTimes_iInter_diff_iInf_subset_terminal σ ht
  simp only [mem_setOf_eq] at h
  rw [mem_singleton_iff, ← h, ENNReal.toReal_ofReal h0]

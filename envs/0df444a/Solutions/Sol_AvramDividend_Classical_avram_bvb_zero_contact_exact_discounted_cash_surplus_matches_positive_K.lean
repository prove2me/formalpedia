-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_zero_contact_exact_discounted_cash_surplus_matches_positive_K
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:20:56.410206+00:00
-- url     : https://prove2.me/submissions/caaecf02-25b6-4e08-b4e7-213795acc102

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bvb_uniform_nojump_exact_discounted_time_compensator_integral
import Theorems.Thm_AvramDividend_Classical_avram_bvb_positivecap_zerocontact_cash_gap_equals_compensator_allowance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory intervalIntegral AvramDividend.Classical
theorem solution (T : ℝ) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, Real.exp (-t)) +
      (1 / 2 : ℝ) * Real.exp (-T) =
      (1 / 2 : ℝ) +
        (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..T, Real.exp (-t)) ∧
    0 < (1 / 2 : ℝ) *
      (∫ t in (0 : ℝ)..T, Real.exp (-t)) := by
  rw [avram_bvb_uniform_nojump_exact_discounted_time_compensator_integral T]
  exact avram_bvb_positivecap_zerocontact_cash_gap_equals_compensator_allowance T hT

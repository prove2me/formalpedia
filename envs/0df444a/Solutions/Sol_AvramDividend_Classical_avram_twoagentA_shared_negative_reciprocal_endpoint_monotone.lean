-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_shared_negative_reciprocal_endpoint_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:40:34.733593+00:00
-- url     : https://prove2.me/submissions/339fd05d-6b65-44aa-b094-2cd824f174e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution :
    Monotone (fun i : ℕ => -(1 / ((i : ℝ) + 1))) := by
  intro i j hij
  have hc : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hij 1
  have hp : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hr := one_div_le_one_div_of_le hp hc
  linarith

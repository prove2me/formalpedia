-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB35_cash_identity_forces_strict_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T15:29:10.185833+00:00
-- url     : https://prove2.me/submissions/f470185b-8931-4c6f-b394-14c5c155be63

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_sigma1_halfband_discounted_strict_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
/-- The exact stopped affine cash identity forces a strict cap-gap excess. -/
theorem solution (y F wC N : ℝ)
  (hylo : (5 / 44 : ℝ) ≤ y)
  (hyhi : y ≤ (1 / 8 : ℝ))
  (hCash : F - wC - N =
      (193419 / 968 : ℝ) * (1 - Real.exp (-(1 / 40000 : ℝ))) +
      Real.exp (-(1 / 40000 : ℝ)) * (y - 4 * y ^ 2 - 15 / 242) -
      (1 / 1936 : ℝ)) :
  ¬ F - wC ≤ N + (1 / 1936 : ℝ) := by
  have hStrict :=
    avram_gbB30_sigma1_halfband_discounted_strict_gap y hylo hyhi
  intro hBound
  linarith

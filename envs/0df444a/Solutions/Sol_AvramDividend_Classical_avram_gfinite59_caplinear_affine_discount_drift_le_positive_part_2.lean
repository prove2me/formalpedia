-- Prove2me | solution 2 for AvramDividend.Classical.avram_gfinite59_caplinear_affine_discount_drift_le_positive_part
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:21:08.12107+00:00
-- url     : https://prove2.me/submissions/2e698daa-408b-46ec-a245-65aed7993101

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

theorem solution
    (c q wb b y : ℝ) (hq : 0 ≤ q)
    (hwb : 0 ≤ wb) (hby : b ≤ y) :
    c - q * (wb + (y - b)) ≤ max c 0 := by
  have hnonneg : 0 ≤ wb + (y - b) := by linarith
  have hdiscount : 0 ≤ q * (wb + (y - b)) :=
    mul_nonneg hq hnonneg
  have hcap : c ≤ max c 0 := le_max_left _ _
  linarith

-- Prove2me | solution 1 for FamousTheorems.nevanlinna_first_main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:41:14.445309+00:00
-- url     : https://prove2.me/submissions/e34a3a6e-7292-4569-8b44-8098fbf9ac19

import Mathlib

theorem solution {f : ℂ → ℂ} (hf : Meromorphic f) (R : ℝ) :
    |ValueDistribution.characteristic f ⊤ R - ValueDistribution.characteristic f⁻¹ ⊤ R|
      ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
  ValueDistribution.characteristic_sub_characteristic_inv_le hf

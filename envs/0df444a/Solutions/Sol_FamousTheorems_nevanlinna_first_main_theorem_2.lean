-- Prove2me | solution 2 for FamousTheorems.nevanlinna_first_main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:42:45.677986+00:00
-- url     : https://prove2.me/submissions/d9290ef9-5fa1-4e06-81e5-6432df1f7575

import Mathlib

theorem solution {f : ℂ → ℂ} (hf : Meromorphic f) (R : ℝ) :
    |ValueDistribution.characteristic f ⊤ R - ValueDistribution.characteristic f⁻¹ ⊤ R|
      ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
  ValueDistribution.characteristic_sub_characteristic_inv_le hf

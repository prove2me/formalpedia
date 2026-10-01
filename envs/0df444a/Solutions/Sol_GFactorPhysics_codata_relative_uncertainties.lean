-- Prove2me | solution 1 for GFactorPhysics.codata_relative_uncertainties
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:20:33.320544+00:00
-- url     : https://prove2.me/submissions/1f753c14-9d34-4501-9a79-6d2a0a17d1da

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution :
    ((1.75e-13 : ℝ) ≤ (3.6e-13 : ℝ) / |(-2.00231930436092 : ℝ)| ∧
      (3.6e-13 : ℝ) / |(-2.00231930436092 : ℝ)| < 1.85e-13) ∧
    ((4.05e-10 : ℝ) ≤ (8.2e-10 : ℝ) / |(-2.00233184123 : ℝ)| ∧
      (8.2e-10 : ℝ) / |(-2.00233184123 : ℝ)| < 4.15e-10) ∧
    ((2.85e-10 : ℝ) ≤ (1.6e-9 : ℝ) / |(5.5856946893 : ℝ)| ∧
      (1.6e-9 : ℝ) / |(5.5856946893 : ℝ)| < 2.95e-10) ∧
    ((2.35e-7 : ℝ) ≤ (9.0e-7 : ℝ) / |(-3.82608552 : ℝ)| ∧
      (9.0e-7 : ℝ) / |(-3.82608552 : ℝ)| < 2.45e-7) := by
  norm_num

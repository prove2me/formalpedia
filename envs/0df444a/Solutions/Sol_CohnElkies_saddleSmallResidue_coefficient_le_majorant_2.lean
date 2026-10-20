-- Prove2me | solution 2 for CohnElkies.saddleSmallResidue_coefficient_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:31:37.939619+00:00
-- url     : https://prove2.me/submissions/84adc1e9-8df4-4fe7-af6b-9b49eb63cb05

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {K C ℓ y : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hℓ : 1 ≤ ℓ)
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    (K / ℓ) *
        Real.exp
          (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
        (2 * y + y ^ 2) * Real.exp (2 * y) ≤
      saddleSmallResidueCoefficientMajorant K C ℓ := by
  unfold saddleSmallResidueCoefficientMajorant
  have hl : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hℓ0 : 0 < ℓ := by linarith
  set Y := Real.log ℓ / 8 + C with hYdef
  set Q := Real.exp (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) with hQ
  have hQ0 : 0 < Q := Real.exp_pos _
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have h1 : 2 * y + y ^ 2 ≤ 2 * Y + Y ^ 2 := by nlinarith
  have h2 : Real.exp (2 * y) / ℓ ≤ Real.exp (2 * C - (3 / 4 : ℝ) * Real.log ℓ) := by
    have e : Real.exp (2 * C - (3 / 4 : ℝ) * Real.log ℓ) = Real.exp (2 * Y) / ℓ := by
      rw [show 2 * C - (3 / 4 : ℝ) * Real.log ℓ = 2 * Y - Real.log ℓ by rw [hYdef]; ring,
        Real.exp_sub, Real.exp_log hℓ0]
    rw [e]
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hℓ0.le
  have h3 : K * Q * (2 * y + y ^ 2) ≤ K * Q * (2 * Y + Y ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hK hQ0.le)
  calc K / ℓ * Q * (2 * y + y ^ 2) * Real.exp (2 * y)
      = K * Q * (2 * y + y ^ 2) * (Real.exp (2 * y) / ℓ) := by ring
    _ ≤ K * Q * (2 * Y + Y ^ 2) * Real.exp (2 * C - (3 / 4 : ℝ) * Real.log ℓ) :=
      mul_le_mul h3 h2 (div_nonneg (Real.exp_pos _).le hℓ0.le) (by positivity)


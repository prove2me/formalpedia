-- Prove2me | solution 1 for CohnElkies.saddleSmallResidue_coefficient_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/bf42824d-b948-4b5c-aa4e-e5afd67d9244

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
namespace CohnElkies
theorem _root_.solution
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
  let Y : ℝ := Real.log ℓ / 8 + C
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  have hY : 0 ≤ Y := by
    try dsimp [Y]
    exact add_nonneg
      (div_nonneg (Real.log_nonneg hℓ)
        (by norm_num)) hC
  have hpoly : 2 * y + y ^ 2 ≤ 2 * Y + Y ^ 2 := by
    have hproduct : 0 ≤ (Y - y) * (Y + y) :=
      mul_nonneg (sub_nonneg.mpr hyupper)
        (add_nonneg hY hy)
    nlinarith
  have hrat :
      Real.exp (2 * Y) / ℓ =
        Real.exp (2 * C - (3 / 4 : ℝ) * Real.log ℓ) := by
    calc
      Real.exp (2 * Y) / ℓ =
          Real.exp (2 * Y) / Real.exp (Real.log ℓ) := by
        rw [Real.exp_log hℓpos]
      _ = Real.exp (2 * Y - Real.log ℓ) := by
        rw [Real.exp_sub]
      _ = Real.exp
          (2 * C - (3 / 4 : ℝ) * Real.log ℓ) := by
        congr 1
        try dsimp [Y]
        ring
  calc
    (K / ℓ) *
        Real.exp
          (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
        (2 * y + y ^ 2) * Real.exp (2 * y) ≤
      (K / ℓ) *
        Real.exp
          (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
        (2 * Y + Y ^ 2) * Real.exp (2 * Y) := by
      gcongr
    _ = K *
        Real.exp
          (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
        (2 * Y + Y ^ 2) *
          (Real.exp (2 * Y) / ℓ) := by
      ring
    _ = saddleSmallResidueCoefficientMajorant K C ℓ := by
      rw [hrat]
      rfl
end CohnElkies

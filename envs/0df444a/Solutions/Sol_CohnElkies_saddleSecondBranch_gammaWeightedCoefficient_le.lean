-- Prove2me | solution 1 for CohnElkies.saddleSecondBranch_gammaWeightedCoefficient_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/9bb9be4e-ff05-498b-b5b5-2865388c0bd2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddle_sqrt_le_one_add
import Theorems.Thm_CohnElkies_saddle_inverse_sqrt_cube_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {q η C : ℝ}
    (hq : 0 < q)
    (hη : 1 ≤ η)
    (hC : 0 < C)
    (hrate : 1 / q ≤ C * η) :
    2 * max (1 : ℝ)
        ((Real.sqrt (q / 6) ^ 3)⁻¹) *
      Real.sqrt (Real.pi / (q / 2)) ≤
        (2 * (1 + (6 * C) ^ 3) *
          (1 + 2 * Real.pi * C)) * η ^ 4 := by
  have hη0 : 0 ≤ η := by linarith
  have hηthree : 1 ≤ η ^ 3 := by
    simpa using!
      (pow_le_pow_left₀
        (show (0 : ℝ) ≤ 1 by norm_num) hη 3)
  have hinverse := saddle_inverse_sqrt_cube_le hq
  have hmax :
      max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) ≤
        1 + (6 / q) ^ 3 := by
    apply max_le
    · have : 0 ≤ (6 / q) ^ 3 := by positivity
      linarith
    · exact hinverse
  have hqscaled : 6 / q ≤ 6 * C * η := by
    calc
      6 / q = 6 * (1 / q) := by ring
      _ ≤ 6 * (C * η) := by gcongr
      _ = 6 * C * η := by ring
  have hmaxpoly :
      max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) ≤
        (1 + (6 * C) ^ 3) * η ^ 3 := by
    calc
      max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) ≤
          1 + (6 / q) ^ 3 := hmax
      _ ≤ 1 + (6 * C * η) ^ 3 := by
        gcongr
      _ ≤ (1 + (6 * C) ^ 3) * η ^ 3 := by
        nlinarith [mul_nonneg
          (show 0 ≤ (6 * C) ^ 3 by positivity)
          (show 0 ≤ η ^ 3 - 1 by linarith)]
  have hpiscaled :
      Real.pi / (q / 2) ≤
        2 * Real.pi * C * η := by
    calc
      Real.pi / (q / 2) =
          (2 * Real.pi) * (1 / q) := by
        field_simp [hq.ne']
      _ ≤ (2 * Real.pi) * (C * η) := by
        gcongr
      _ = 2 * Real.pi * C * η := by ring
  have hsqrt :
      Real.sqrt (Real.pi / (q / 2)) ≤
        (1 + 2 * Real.pi * C) * η := by
    calc
      Real.sqrt (Real.pi / (q / 2)) ≤
          1 + Real.pi / (q / 2) :=
        saddle_sqrt_le_one_add (by positivity)
      _ ≤ 1 + 2 * Real.pi * C * η := by
        linarith
      _ ≤ (1 + 2 * Real.pi * C) * η := by
        nlinarith
  calc
    2 * max (1 : ℝ)
        ((Real.sqrt (q / 6) ^ 3)⁻¹) *
      Real.sqrt (Real.pi / (q / 2)) ≤
      2 * ((1 + (6 * C) ^ 3) * η ^ 3) *
        ((1 + 2 * Real.pi * C) * η) := by
      gcongr
    _ = (2 * (1 + (6 * C) ^ 3) *
          (1 + 2 * Real.pi * C)) * η ^ 4 := by
      ring
end CohnElkies

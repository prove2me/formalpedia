-- Prove2me | solution 2 for CohnElkies.saddle_cubic_translation_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:04:05.566403+00:00
-- url     : https://prove2.me/submissions/fcfeccda-1479-43c9-988c-da0cf49cdc9a

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
    (u T : ℝ) (A B C : ℂ)
    (hA : ‖A‖ ≤ 3 * (1 + |u|) ^ 2)
    (hB : ‖B‖ ≤ 3 * (1 + |u|) ^ 2)
    (hC : ‖C‖ ≤ 1) :
    ‖(T : ℂ) * A + (T : ℂ) ^ 2 * B +
        C * (T : ℂ) ^ 3‖ ≤
      9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
  have hu : 0 ≤ 3 * (1 + |u|) ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ 3 * (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
  have nT : ‖(T : ℂ)‖ = |T| := Complex.norm_real T
  calc ‖(T : ℂ) * A + (T : ℂ) ^ 2 * B + C * (T : ℂ) ^ 3‖
      ≤ ‖(T : ℂ) * A‖ + ‖(T : ℂ) ^ 2 * B‖ + ‖C * (T : ℂ) ^ 3‖ := norm_add₃_le
    _ = |T| * ‖A‖ + |T| ^ 2 * ‖B‖ + ‖C‖ * |T| ^ 3 := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, nT]
    _ ≤ 9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
        have hT := abs_nonneg T
        have hT2 : |T| ^ 2 ≤ |T| + |T| ^ 3 := by nlinarith [sq_nonneg (|T| - 1)]
        have a1 : |T| * ‖A‖ ≤ |T| * (3 * (1 + |u|) ^ 2) := mul_le_mul_of_nonneg_left hA hT
        have a2 : |T| ^ 2 * ‖B‖ ≤ (|T| + |T| ^ 3) * (3 * (1 + |u|) ^ 2) :=
          mul_le_mul (hT2) hB (norm_nonneg _) (by positivity)
        have a3 : ‖C‖ * |T| ^ 3 ≤ (3 * (1 + |u|) ^ 2) * |T| ^ 3 :=
          mul_le_mul_of_nonneg_right (hC.trans h1) (by positivity)
        nlinarith [pow_nonneg hT 3]


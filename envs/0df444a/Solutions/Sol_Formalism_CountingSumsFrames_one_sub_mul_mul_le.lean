-- Prove2me | solution 1 for Formalism.CountingSumsFrames.one_sub_mul_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:55.168843+00:00
-- url     : https://prove2.me/submissions/aceb8983-561c-4730-a86a-594fb5b88e0b

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrameMultinomialBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Real
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (y P W C x : ℝ) (n : ℕ) (hW : 0 ≤ W) (hP0 : 0 ≤ P) (hC : 0 ≤ C)
    (hPle : P ≤ (1 + x) ^ n * C) (hkey : (1 - y) * (1 + x) ^ n ≤ 1) : (1 - y) * (P * W) ≤ C * W := by
  have hPW : 0 ≤ P * W := mul_nonneg hP0 hW
  have hCW : 0 ≤ C * W := mul_nonneg hC hW
  by_cases h : 1 - y ≤ 0
  · nlinarith
  · rw [not_le] at h
    calc (1 - y) * (P * W) ≤ (1 - y) * (((1 + x) ^ n * C) * W) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPle hW) h.le
      _ = ((1 - y) * (1 + x) ^ n) * (C * W) := by ring
      _ ≤ 1 * (C * W) := mul_le_mul_of_nonneg_right hkey hCW
      _ = C * W := one_mul _
end Formalism.CountingSumsFrames

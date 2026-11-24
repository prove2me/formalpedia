-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.pow_le_sqrt_of_rpow_le_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:45.760896+00:00
-- url     : https://prove2.me/submissions/a18157de-55a0-4d6a-a6eb-965285b71cce

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMainB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) (x X : ℝ) (hx3 : 3 ≤ x) (hx : (19200 / ε) ^ (12 / ε) ≤ x)
    (hX : 0 < X) (hlog : x ^ (ε / 6) ≤ Real.log X) : x ^ 800 ≤ X ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hε12 : 0 < ε / 12 := by positivity
  have hy1 : 1 < x ^ (ε / 12) := Real.one_lt_rpow hx1 hε12
  have hy0 : 0 < x ^ (ε / 12) := by linarith
  have hK0 : 0 < 19200 / ε := by positivity
  have hy : 19200 / ε ≤ x ^ (ε / 12) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hK0.le (12 / ε)) hx hε12.le
    rwa [← Real.rpow_mul hK0.le, show 12 / ε * (ε / 12) = 1 by field_simp, Real.rpow_one] at h
  have hlogx : Real.log x = 12 / ε * Real.log (x ^ (ε / 12)) := by
    rw [Real.log_rpow hx0]
    field_simp
  have hy2 : x ^ (ε / 6) = (x ^ (ε / 12)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have hlogy0 : 0 < Real.log (x ^ (ε / 12)) := Real.log_pos hy1
  have hlogy : Real.log (x ^ (ε / 12)) ≤ x ^ (ε / 12) :=
    (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
  have key : 1600 * Real.log x ≤ Real.log X := by
    rw [hlogx]
    calc 1600 * (12 / ε * Real.log (x ^ (ε / 12))) = 19200 / ε * Real.log (x ^ (ε / 12)) := by ring
      _ ≤ x ^ (ε / 12) * Real.log (x ^ (ε / 12)) := mul_le_mul_of_nonneg_right hy hlogy0.le
      _ ≤ x ^ (ε / 12) * x ^ (ε / 12) := mul_le_mul_of_nonneg_left hlogy hy0.le
      _ = x ^ (ε / 6) := by rw [hy2]; ring
      _ ≤ Real.log X := hlog
  rw [← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hX _), Real.log_pow,
    Real.log_rpow hX]
  push_cast
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

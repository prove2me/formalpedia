-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_num_third
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:12.457994+00:00
-- url     : https://prove2.me/submissions/39a24460-0c79-4ace-900e-82688e53d4d4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (x : ℝ) (hx : 3 ≤ x) :
    (x ^ 398 + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 399 ≤ 802 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hp : 0 < x ^ 398 := by positivity
  have hp1 : 1 ≤ x ^ 398 := one_le_pow₀ hx1
  have hA : x ^ 400 + x ^ 400 * (1 / x ^ 2) = x ^ 398 * (x ^ 2 + 1) := by
    field_simp
  have hsq : x ^ 2 + 1 ≤ x ^ 3 := by nlinarith
  have hA1 : x ^ 398 * (x ^ 2 + 1) ≤ x ^ 401 := by
    have : x ^ 401 = x ^ 398 * x ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsq hp.le
  have hApos : 0 < x ^ 398 * (x ^ 2 + 1) := by positivity
  have hAge : 1 ≤ x ^ 398 * (x ^ 2 + 1) := by nlinarith
  have hL0 : 0 ≤ Real.log (x ^ 398 * (x ^ 2 + 1)) := Real.log_nonneg hAge
  have hL1 : Real.log (x ^ 398 * (x ^ 2 + 1)) ≤ 401 * x := by
    calc Real.log (x ^ 398 * (x ^ 2 + 1)) ≤ Real.log (x ^ 401) := Real.log_le_log hApos hA1
      _ = 401 * Real.log x := by rw [Real.log_pow]; norm_num
      _ ≤ 401 * x := by
        have := Real.log_le_sub_one_of_pos hx0
        linarith
  have hx399 : x ≤ x ^ 399 := by
    have : x ^ 399 = x * x ^ 398 := by ring
    rw [this]
    nlinarith
  rw [hA, div_le_iff₀ (by positivity : (0:ℝ) < x ^ 399)]
  calc (x ^ 398 + 1) * Real.log (x ^ 398 * (x ^ 2 + 1))
      ≤ (x ^ 398 + 1) * (401 * x) := mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = 401 * x ^ 399 + 401 * x := by ring
    _ ≤ 802 * x ^ 399 := by linarith
end Formalism.HermitianLattices.Ext.BoxTail

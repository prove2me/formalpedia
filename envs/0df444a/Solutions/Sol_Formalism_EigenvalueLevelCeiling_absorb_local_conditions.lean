-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.absorb_local_conditions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:47.970884+00:00
-- url     : https://prove2.me/submissions/8d3b8119-b0db-499c-8071-bd73613c9405

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : AbsorbOn := by
  unfold AbsorbOn
  intro C Cb L xe f m b k ws Se Y X2 bad hC hCb hL hLx hf hm hb hk hlk hws0 hws hSe hkSe hY hlY
    hYmb hkX hbad
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hf0 : (0:ℝ) ≤ f := by linarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hX2 : (0:ℝ) < X2 := by linarith
  have hxe : (1:ℝ) ≤ xe := by linarith
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hfmb : 0 ≤ f * m * b := mul_nonneg (mul_nonneg hf0 hm0) hb.le
  have hQ : 0 ≤ f * m * b * L := mul_nonneg hfmb hL0
  have hLxe : 1 ≤ L * xe := one_le_mul_of_one_le_of_one_le hL hxe
  have fmb_le : f * m * b ≤ f * m * b * L * xe := by
    have := mul_le_mul_of_nonneg_left hLxe hfmb
    linarith
  have QL_le : f * m * b * L * L ≤ f * m * b * L * xe := mul_le_mul_of_nonneg_left hLx hQ
  have hQx : 0 ≤ f * m * b * L * xe := by linarith
  have hA0 : 0 ≤ Real.log k * m * ws := mul_nonneg (mul_nonneg hlogk hm0) hws0
  have hB0 : 0 ≤ f * k * Se := mul_nonneg (mul_nonneg hf0 hk0.le) hSe
  have a1 : Real.log k * (m * ws) ≤ L * (m * (2 * f * b)) :=
    mul_le_mul hlk (mul_le_mul_of_nonneg_left hws hm0) (mul_nonneg hm0 hws0) hL0
  have a2 : f * (k * Se * L) ≤ f * (m * b) := mul_le_mul_of_nonneg_left hkSe hf0
  have t1a : (Real.log k * m * ws + f * k * Se) * Real.log Y ≤
      (Real.log k * m * ws + f * k * Se) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (add_nonneg hA0 hB0)
  have t1b : Real.log k * m * ws * (2 * L) ≤ 2 * (f * m * b * L) * (2 * L) := by
    have h1 : Real.log k * m * ws ≤ 2 * (f * m * b * L) := by linarith
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have t1 : (Real.log k * m * ws + f * k * Se) * Real.log Y ≤ 6 * (f * m * b * L * xe) := by
    linarith
  have u1 : C * ((Real.log k * m * ws + f * k * Se) * Real.log Y) ≤
      C * (6 * (f * m * b * L * xe)) := mul_le_mul_of_nonneg_left t1 hC0
  have fb_le : f * b ≤ f * m * b := by
    have := mul_le_mul_of_nonneg_left hm (mul_nonneg hf0 hb.le)
    linarith
  have ws_le : ws ≤ 2 * (f * m * b * L * xe) := by linarith
  have u2 : C ^ 2 * ws ≤ C ^ 2 * (2 * (f * m * b * L * xe)) :=
    mul_le_mul_of_nonneg_left ws_le (by positivity)
  have mb_le : m * b ≤ f * m * b * L * xe := by
    have := mul_le_mul_of_nonneg_left hf (mul_nonneg hm0 hb.le)
    linarith
  have u3 : C * (m * b) ≤ C * (f * m * b * L * xe) := mul_le_mul_of_nonneg_left mb_le hC0
  have u4 : C * ws ≤ C * (2 * (f * m * b * L * xe)) := mul_le_mul_of_nonneg_left ws_le hC0
  have u5a : f * m * b * L * xe ≤ C * (f * m * b * L * xe) := le_mul_of_one_le_left hQx hC
  have u6a : Cb * (f * m * b * L) ≤ Cb * (f * m * b * L * xe) := by
    have := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hQ hxe) hCb
    linarith
  have u8 : 0 ≤ C * (f * m * b * L * xe) := mul_nonneg hC0 hQx
  have t2e : C * k * ws * (C / k) = C ^ 2 * ws := by
    have : k ≠ 0 := hk0.ne'
    field_simp
  have t4 : 2.04 * (C * k * ws) / X2 ≤ 2.04 * (C * ws) := by
    rw [div_le_iff₀ hX2]
    have := mul_le_mul_of_nonneg_left hkX (mul_nonneg hC0 hws0)
    linarith
  linarith
end Formalism.EigenvalueLevelCeiling

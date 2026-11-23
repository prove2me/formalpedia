-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.absorb_local_conditions_exact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:48.475968+00:00
-- url     : https://prove2.me/submissions/5d899132-b40b-477c-a177-c70fe66c364b

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_ErrSumGoodExact
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsComposeGeneral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverP
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverPSqTail
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
private theorem lead_exact : LeadExact := by
  intro C L f m b k ws Se Y X2 hC hf hm hb hk hws0 hws hSe hkS hY hlY hYb hX2
  have hl4 : Real.log 4 < 1.3863 := by
    have h := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith
  have hC0 : 0 ≤ C := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 < k := by linarith
  have hX0 : 0 < X2 := by linarith
  have hY0 : 0 < Y := by linarith
  have hlk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hmb : 0 ≤ m * b := mul_nonneg hm0 hb.le
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb.le
  have e1 : C * (Real.log k * m * ws) * Real.log Y ≤ C * (Real.log k * m * ws) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (mul_nonneg hC0 (mul_nonneg (mul_nonneg hlk hm0) hws0))
  have e2 : C * (f * k * Se) * Real.log Y ≤ C * (f * k * Se) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (mul_nonneg hC0 (mul_nonneg (mul_nonneg hf0 hk0.le) hSe))
  have e2b : C * f * (k * Se * L) ≤ C * f * (m * b) :=
    mul_le_mul_of_nonneg_left hkS (mul_nonneg hC0 hf0)
  have e3 : C * k * ws * (C / k) = C ^ 2 * ws := by
    rw [show C * k * ws * (C / k) = C ^ 2 * ws * (k / k) by ring, div_self hk0.ne', mul_one]
  have e3b : C ^ 2 * ws ≤ C ^ 2 * (2 * (f * b)) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg C)
  have hfbm : f * b ≤ f * b * m := le_mul_of_one_le_right hfb hm
  have e3c : C ^ 2 * (f * b) ≤ C ^ 2 * (f * b * m) := mul_le_mul_of_nonneg_left hfbm (sq_nonneg C)
  have hmbf : m * b ≤ f * (m * b) := le_mul_of_one_le_left hmb hf
  have e4 : C * (m * b) ≤ C * (f * (m * b)) := mul_le_mul_of_nonneg_left hmbf hC0
  have hCws : 0 ≤ C * ws := mul_nonneg hC0 hws0
  have hkX : k / X2 ≤ 1 := (div_le_one hX0).mpr hX2
  have e5 : C * k * ws / X2 ≤ C * ws := by
    calc C * k * ws / X2 = C * ws * (k / X2) := by ring
      _ ≤ C * ws * 1 := mul_le_mul_of_nonneg_left hkX hCws
      _ = C * ws := mul_one _
  have e5' : 2.04 * (C * k * ws) / X2 ≤ 2.04 * (C * ws) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left e5 (by norm_num)
  have e5b : C * ws ≤ C * (2 * (f * b)) := mul_le_mul_of_nonneg_left (by linarith) hC0
  have e5c : C * (f * b) ≤ C * (f * b * m) := mul_le_mul_of_nonneg_left hfbm hC0
  have e6 : Real.log 4 * Y ≤ 1.3863 * Y := mul_le_mul_of_nonneg_right hl4.le hY0.le
  have hCf : 1 ≤ C * f := one_le_mul_of_one_le_of_one_le hC hf
  have e6b : m * b ≤ C * f * (m * b) := le_mul_of_one_le_left hmb hCf
  have e7 : 0 ≤ C * f * (m * b) := mul_nonneg (mul_nonneg hC0 hf0) hmb
  linarith
end Formalism.EigenvalueLevelCeiling
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : AbsorbOnExact := by
  intro C Cb L xe f m b k ws Se Y X2 bad hC hCb hL hxe hf hm hb hk hlk hws0 hws hSe hkS hY hlY hYb hX2 hbad
  have hlead := lead_exact C L f m b k ws Se Y X2 hC hf hm hb hk hws0 hws hSe hkS hY hlY hYb hX2
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hZ : 0 ≤ f * m * b := mul_nonneg (mul_nonneg hf0 hm0) hb.le
  have hxe1 : 1 ≤ xe := by linarith
  have hxL : 1 ≤ xe * L := one_le_mul_of_one_le_of_one_le hxe1 hL
  have a1 : Real.log k * (C * L * (m * ws)) ≤ L * (C * L * (m * ws)) :=
    mul_le_mul_of_nonneg_right hlk (mul_nonneg (mul_nonneg hC0 hL0) (mul_nonneg hm0 hws0))
  have a2 : C * L * L * (m * ws) ≤ C * L * L * (m * (2 * f * b)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hws hm0) (mul_nonneg (mul_nonneg hC0 hL0) hL0)
  have a3 : C * (f * m * b) * (L * L) ≤ C * (f * m * b) * (xe * L) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxe hL0) (mul_nonneg hC0 hZ)
  have hq : 0 ≤ 4 * C ^ 2 + 17 * C := add_nonneg (by positivity) (by linarith)
  have a5 : (4 * C ^ 2 + 17 * C) * (f * m * b) ≤ (4 * C ^ 2 + 17 * C) * (f * m * b) * (xe * L) :=
    le_mul_of_one_le_right (mul_nonneg hq hZ) hxL
  have a6 : Cb * (f * m * b * L) ≤ Cb * (f * m * b * L) * xe :=
    le_mul_of_one_le_right (mul_nonneg hCb (mul_nonneg hZ hL0)) hxe1
  have a7 : 12 * (f * m * b) ≤ 12 * (f * m * b) * (xe * L) :=
    le_mul_of_one_le_right (by linarith) hxL
  linarith
end Formalism.EigenvalueLevelCeiling

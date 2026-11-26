-- Prove2me | solution 1 for FirstPassageLinearTransport.eventuallyLogAddRpowLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:21.429108+00:00
-- url     : https://prove2.me/submissions/763cb530-cfe6-4ad7-88a6-ce3cedd29c90

import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
import Definitions.Def_FirstPassageLinearTransport_StretchedLogLanding
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A C c a delta : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : 0 < c)
    (hdelta : delta < 1) (ha : delta < a) :
    ∀ᶠ x : ℝ in atTop,
      A * Real.log x + C * x ^ (1 - a) ≤
        c * x ^ (1 - delta) := by
  have hs : 0 < 1 - delta := sub_pos.mpr hdelta
  let q1 := c / (2 * (A + 1))
  let q2 := c / (2 * (C + 1))
  have hq1 : 0 < q1 := by dsimp [q1]; positivity
  have hq2 : 0 < q2 := by dsimp [q2]; positivity
  have hlog := (isLittleO_log_rpow_atTop hs).bound hq1
  have hpow := (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).eventually
    (Iio_mem_nhds hq2)
  filter_upwards [hlog, hpow, eventually_ge_atTop (1 : ℝ)] with x hxlog hxpow hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have htarget0 : 0 ≤ x ^ (1 - delta) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0,
    Real.norm_eq_abs, abs_of_nonneg htarget0] at hxlog
  have hfirst : A * Real.log x ≤ c / 2 * x ^ (1 - delta) := by
    have hmul := mul_le_mul_of_nonneg_left hxlog hA
    dsimp [q1] at hmul
    have hfrac : A / (A + 1) ≤ 1 := by
      apply (div_le_one (by linarith)).2
      linarith
    have hcoef : A * (c / (2 * (A + 1))) ≤ c / 2 := by
      rw [show A * (c / (2 * (A + 1))) =
        (c / 2) * (A / (A + 1)) by field_simp]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac
        (div_nonneg hc.le (by norm_num : (0 : ℝ) ≤ 2))
    calc
      A * Real.log x ≤ A * (q1 * x ^ (1 - delta)) := hmul
      _ = (A * q1) * x ^ (1 - delta) := by ring
      _ ≤ (c / 2) * x ^ (1 - delta) :=
        mul_le_mul_of_nonneg_right hcoef htarget0
  have hxpow0 : 0 ≤ x ^ (delta - a) := Real.rpow_nonneg hx0.le _
  have hpowRewrite : x ^ (-(a - delta)) = x ^ (delta - a) := by
    congr 1
    ring
  rw [hpowRewrite] at hxpow
  have hsecond : C * x ^ (1 - a) ≤ c / 2 * x ^ (1 - delta) := by
    have hid : x ^ (1 - a) = x ^ (1 - delta) * x ^ (delta - a) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_left hxpow.le hC
    have hfrac : C / (C + 1) ≤ 1 := by
      apply (div_le_one (by linarith)).2
      linarith
    have hcoef : C * q2 ≤ c / 2 := by
      dsimp [q2]
      rw [show C * (c / (2 * (C + 1))) =
        (c / 2) * (C / (C + 1)) by field_simp]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac
        (div_nonneg hc.le (by norm_num : (0 : ℝ) ≤ 2))
    calc
      C * (x ^ (1 - delta) * x ^ (delta - a)) =
          x ^ (1 - delta) * (C * x ^ (delta - a)) := by ring
      _ ≤ x ^ (1 - delta) * (C * q2) :=
        mul_le_mul_of_nonneg_left hmul htarget0
      _ ≤ x ^ (1 - delta) * (c / 2) :=
        mul_le_mul_of_nonneg_left hcoef htarget0
      _ = c / 2 * x ^ (1 - delta) := by ring
  nlinarith
end FirstPassageLinearTransport

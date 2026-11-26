-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_sqrt_mul_log_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:13.513806+00:00
-- url     : https://prove2.me/submissions/55bd3ebf-0cff-45e0-b21e-bef56e48bda7

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ M : ℕ in atTop,
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) ≤
        delta * ((M : ℝ) + 2) := by
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ))
      (1 / 2 : ℝ) (by norm_num)).bound hdelta
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall] with M hsmall
  let x : ℝ := (M : ℝ) + 2
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxhalf0 : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hloghalf0 : 0 ≤ Real.log x ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hlog0 _
  rw [Real.norm_eq_abs, abs_of_nonneg hloghalf0,
    Real.norm_eq_abs, abs_of_nonneg hxhalf0] at hsmall
  rw [Real.sqrt_mul hx0.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  calc
    x ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ) ≤
        x ^ (1 / 2 : ℝ) * (delta * x ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsmall hxhalf0
    _ = delta * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
    _ = delta * x := by
      rw [← Real.rpow_add hx0]
      norm_num
end FirstPassageLinearTransport

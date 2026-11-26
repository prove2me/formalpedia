-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_exp_log_sq_sub_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:25.548828+00:00
-- url     : https://prove2.me/submissions/bfacfda1-98e2-423d-9ea7-16ce974681c3

import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Definitions.Def_FirstPassageLinearTransport_Scalar
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
open Filter Asymptotics
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    Tendsto (fun x : ℝ =>
      Real.exp (A * (Real.log x) ^ 2 - c * x ^ s))
      atTop (nhds 0) := by
  let q := c / (2 * (|A| + 1))
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop 2 hs).bound hq
  have hupper : ∀ᶠ x : ℝ in atTop,
      Real.exp (A * (Real.log x) ^ 2 - c * x ^ s) ≤
        Real.exp (-(c / 2 * x ^ s)) := by
    filter_upwards [hlo, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hxs0 : 0 ≤ x ^ s := Real.rpow_nonneg (zero_le_one.trans hx1) s
    rw [Real.rpow_two] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log x)),
      Real.norm_eq_abs, abs_of_nonneg hxs0] at hx
    have hA : A ≤ |A| + 1 := by linarith [le_abs_self A]
    have hlogSq : 0 ≤ Real.log x ^ (2 : ℕ) := sq_nonneg _
    have hmain : A * Real.log x ^ (2 : ℕ) ≤ c / 2 * x ^ s := by
      have h1 := mul_le_mul_of_nonneg_right hA hlogSq
      have h2 : (|A| + 1) * (q * x ^ s) = c / 2 * x ^ s := by
        dsimp [q]
        field_simp
      calc
        A * Real.log x ^ (2 : ℕ) ≤
            (|A| + 1) * Real.log x ^ (2 : ℕ) := h1
        _ ≤ (|A| + 1) * (q * x ^ s) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
        _ = c / 2 * x ^ s := h2
    apply Real.exp_le_exp.2
    norm_num at hmain ⊢
    linarith
  have htPower : Tendsto (fun x : ℝ => c / 2 * x ^ s) atTop atTop :=
    (tendsto_rpow_atTop hs).const_mul_atTop (by positivity)
  have htUpper : Tendsto (fun x : ℝ =>
      Real.exp (-(c / 2 * x ^ s))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp htPower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htUpper
  · filter_upwards with x
    exact Real.exp_pos _ |>.le
  · exact hupper
end FirstPassageLinearTransport

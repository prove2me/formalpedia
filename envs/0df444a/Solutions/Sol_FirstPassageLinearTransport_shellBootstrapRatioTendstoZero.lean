-- Prove2me | solution 1 for FirstPassageLinearTransport.shellBootstrapRatioTendstoZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:11.821648+00:00
-- url     : https://prove2.me/submissions/3748d2d4-7d5e-40a6-9cd7-502da83845c6

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
import Theorems.Thm_FirstPassageLinearTransport_shellBootstrapRatioLeExp
import Theorems.Thm_FirstPassageLinearTransport_scheduleDensityLower
import Theorems.Thm_FirstPassageLinearTransport_bootstrapLogBoundScheduleLe
import Theorems.Thm_FirstPassageLinearTransport_shiftedDensityScaleLower
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
import Theorems.Thm_FirstPassageLinearTransport_shellExceptionalRatio_nonneg
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_tendsto_exp_log_sq_sub_rpow
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
    {r eta chi Dc omega : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hdensity : densityGamma omega chi < 1) :
    Tendsto (fun M =>
      shellExceptionalRatio (shellBootstrap p omega M) M)
      atTop (nhds 0) := by
  let gamma := densityGamma omega chi
  let s := 1 - gamma
  let A := bootstrapScheduleA p chi Dc omega
  let B := 2 * (|A| + 1)
  let c := Real.log 2 * Dc / 5
  let C0 := Real.log 2 + 2 * (|A| + 1)
  have hs : 0 < s := by dsimp [s, gamma]; linarith
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have htReal := tendsto_exp_log_sq_sub_rpow (A := B) hc hs
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop (4 : ℝ)
      tendsto_natCast_atTop_atTop
  have htCore : Tendsto (fun M : ℕ =>
      Real.exp (B * (Real.log ((M : ℝ) + 4)) ^ 2 -
        c * ((M : ℝ) + 4) ^ s)) atTop (nhds 0) :=
    htReal.comp hxT
  have htUpper : Tendsto (fun M : ℕ =>
      Real.exp (C0 + B * (Real.log ((M : ℝ) + 4)) ^ 2 -
        c * ((M : ℝ) + 4) ^ s)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _M : ℕ => Real.exp C0)
        atTop (nhds (Real.exp C0)) := tendsto_const_nhds
    have hmul : Tendsto (fun M : ℕ => Real.exp C0 *
        Real.exp (B * (Real.log ((M : ℝ) + 4)) ^ 2 -
          c * ((M : ℝ) + 4) ^ s)) atTop
        (nhds (Real.exp C0 * 0)) := hconst.mul htCore
    convert hmul using 1
    · funext M
      rw [show C0 + B * Real.log ((M : ℝ) + 4) ^ 2 -
          c * ((M : ℝ) + 4) ^ s =
        C0 + (B * Real.log ((M : ℝ) + 4) ^ 2 -
          c * ((M : ℝ) + 4) ^ s) by ring,
        Real.exp_add]
    · simp
  have hupper : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (shellBootstrap p omega M) M ≤
        Real.exp (C0 + B * (Real.log ((M : ℝ) + 4)) ^ 2 -
          c * ((M : ℝ) + 4) ^ s) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    let R := stageCount omega M
    let x := Real.log ((M : ℝ) + 4)
    have hbase := shellBootstrapRatioLeExp p hchi0 hchir hchi1
      hDc0 hDc1 hDcRate hchiDc R M
    have hlog := bootstrapLogBoundScheduleLe p hchi0 hchir hchi1
      hDc0 hDc1 homega0.le M
    have hD := scheduleDensityLower hchi0 hchi1 hDc0.le
      homega0.le M
    have hscale := shiftedDensityScaleLower gamma hM
    have hDM : Dc / 5 * ((M : ℝ) + 4) ^ s ≤
        bootstrapD chi Dc R * M := by
      have h1 := mul_le_mul_of_nonneg_left hscale hDc0.le
      have h2 := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg M)
      dsimp [s]
      nlinarith
    have hxSq : (x + 1) ^ 2 ≤ 2 * x ^ 2 + 2 := by
      nlinarith [sq_nonneg (x - 1)]
    have hA : A ≤ |A| + 1 := by linarith [le_abs_self A]
    have hAx : A * (x + 1) ^ 2 ≤
        (|A| + 1) * (2 * x ^ 2 + 2) := by
      exact (mul_le_mul_of_nonneg_right hA (sq_nonneg (x + 1))).trans
        (mul_le_mul_of_nonneg_left hxSq (by positivity))
    apply hbase.trans
    apply Real.exp_le_exp.2
    dsimp [shellBootstrap, R] at hbase
    dsimp [gamma, s, A, B, c, C0, x] at hlog hD hDM hAx ⊢
    have hpref := hlog.trans hAx
    have hdecay := mul_le_mul_of_nonneg_left hDM
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    nlinarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htUpper
  · filter_upwards with M
    exact shellExceptionalRatio_nonneg _ _
  · exact hupper
end FirstPassageLinearTransport

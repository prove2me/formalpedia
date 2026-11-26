-- Prove2me | solution 1 for FirstPassageLinearTransport.eventuallyShellBootstrapRatioLeStretched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:49.372207+00:00
-- url     : https://prove2.me/submissions/7ffbf967-fa46-46df-b3c9-7081c7f12dff

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
set_option maxHeartbeats 2000000
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta chi Dc omega sigma : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hsigma0 : 0 < sigma)
    (hsigma : sigma < 1 - densityGamma omega chi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (shellBootstrap p omega M) M ≤
        2 * Real.exp (-c * ((M : ℝ) + 4) ^ sigma) := by
  let gamma := densityGamma omega chi
  let s := 1 - gamma
  let A := bootstrapScheduleA p chi Dc omega
  let B := 2 * (|A| + 1)
  let c0 := Real.log 2 * Dc / 5
  let C0 := Real.log 2 + 2 * (|A| + 1)
  let c := c0 / 4
  have hs : 0 < s := by dsimp [s, gamma]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  let q := c0 / (8 * (|B| + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hlogSmallReal :=
    (isLittleO_log_rpow_rpow_atTop (s := s) 2 hs).bound hq
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop (4 : ℝ)
      tendsto_natCast_atTop_atTop
  have hlogSmall := hxT.eventually hlogSmallReal
  have hpowT : Tendsto (fun M : ℕ => ((M : ℝ) + 4) ^ s)
      atTop atTop := (tendsto_rpow_atTop hs).comp hxT
  have hconstLarge : ∀ᶠ M : ℕ in atTop,
      8 * (|C0| + 1) / c0 ≤ ((M : ℝ) + 4) ^ s :=
    (tendsto_atTop.1 hpowT) _
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlogSmall, hconstLarge,
    eventually_ge_atTop (1 : ℕ)] with M hlogSmall hconstLarge hM
  let R := stageCount omega M
  let x : ℝ := (M : ℝ) + 4
  let lx := Real.log x
  have hx : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hxs0 : 0 ≤ x ^ s := Real.rpow_nonneg (zero_le_one.trans hx) _
  have hlx0 : 0 ≤ lx := by dsimp [lx]; exact Real.log_nonneg hx
  have hbase := shellBootstrapRatioLeExp p hchi0 hchir hchi1
    hDc0 hDc1 hDcRate hchiDc R M
  have hlog := bootstrapLogBoundScheduleLe p hchi0 hchir hchi1
    hDc0 hDc1 homega0.le M
  have hD := scheduleDensityLower hchi0 hchi1 hDc0.le
    homega0.le M
  have hscale := shiftedDensityScaleLower gamma hM
  have hDM : Dc / 5 * x ^ s ≤ bootstrapD chi Dc R * M := by
    have h1 := mul_le_mul_of_nonneg_left hscale hDc0.le
    have h2 := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg M)
    dsimp [x, s]
    nlinarith
  have hxSq : (lx + 1) ^ 2 ≤ 2 * lx ^ 2 + 2 := by
    nlinarith [sq_nonneg (lx - 1)]
  have hAle : A ≤ |A| + 1 := by linarith [le_abs_self A]
  have hAx : A * (lx + 1) ^ 2 ≤
      (|A| + 1) * (2 * lx ^ 2 + 2) := by
    exact (mul_le_mul_of_nonneg_right hAle (sq_nonneg (lx + 1))).trans
      (mul_le_mul_of_nonneg_left hxSq (by positivity))
  have hexpBound :
      shellExceptionalRatio (shellBootstrap p omega M) M ≤
        Real.exp (C0 + B * lx ^ 2 - c0 * x ^ s) := by
    apply hbase.trans
    apply Real.exp_le_exp.2
    dsimp [shellBootstrap, R] at hbase
    dsimp [gamma, s, A, B, c0, C0, x, lx] at hlog hD hDM hAx ⊢
    have hpref := hlog.trans hAx
    have hdecay := mul_le_mul_of_nonneg_left hDM
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlx0 2),
    Real.norm_eq_abs, abs_of_nonneg hxs0] at hlogSmall
  have hBLog : B * lx ^ (2 : ℕ) ≤ c0 / 8 * x ^ s := by
    have hBabs : B ≤ |B| + 1 := by linarith [le_abs_self B]
    have hmul := mul_le_mul_of_nonneg_left hlogSmall
      (by positivity : 0 ≤ |B| + 1)
    dsimp [q] at hmul
    have hden : |B| + 1 ≠ 0 := ne_of_gt (by positivity)
    have hreform : (|B| + 1) * (c0 / (8 * (|B| + 1)) * x ^ s) =
        c0 / 8 * x ^ s := by
      field_simp [hden]
    rw [hreform] at hmul
    exact (mul_le_mul_of_nonneg_right hBabs (sq_nonneg lx)).trans
      (by simpa [mul_assoc] using hmul)
  have hC0 : C0 ≤ c0 / 8 * x ^ s := by
    have hcross := mul_le_mul_of_nonneg_left hconstLarge hc0.le
    have hCabs : C0 ≤ |C0| + 1 := by linarith [le_abs_self C0]
    have hrewrite : c0 * (8 * (|C0| + 1) / c0) =
        8 * (|C0| + 1) := by field_simp [hc0.ne']
    rw [hrewrite] at hcross
    change 8 * (|C0| + 1) ≤ c0 * x ^ s at hcross
    have hdiv := (div_le_div_iff_of_pos_right
      (by norm_num : (0 : ℝ) < 8)).2 hcross
    calc
      C0 ≤ |C0| + 1 := hCabs
      _ = (8 * (|C0| + 1)) / 8 := by ring
      _ ≤ (c0 * x ^ s) / 8 := hdiv
      _ = c0 / 8 * x ^ s := by ring
  have hsigPow : x ^ sigma ≤ x ^ s :=
    Real.rpow_le_rpow_of_exponent_le hx (by dsimp [s]; exact hsigma.le)
  have hexponents :
      C0 + B * lx ^ 2 - c0 * x ^ s ≤
        Real.log 2 - c * x ^ sigma := by
    have hlog2pos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    dsimp [c]
    nlinarith
  calc
    shellExceptionalRatio (shellBootstrap p omega M) M ≤
        Real.exp (C0 + B * lx ^ 2 - c0 * x ^ s) := hexpBound
    _ ≤ Real.exp (Real.log 2 - c * x ^ sigma) :=
      Real.exp_le_exp.2 hexponents
    _ = 2 * Real.exp (-c * x ^ sigma) := by
      rw [show Real.log 2 - c * x ^ sigma =
        Real.log 2 + (-c * x ^ sigma) by ring, Real.exp_add,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
end FirstPassageLinearTransport

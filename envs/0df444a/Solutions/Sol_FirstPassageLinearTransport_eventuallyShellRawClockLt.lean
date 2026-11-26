-- Prove2me | solution 1 for FirstPassageLinearTransport.eventuallyShellRawClockLt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:12.187072+00:00
-- url     : https://prove2.me/submissions/a8fd1f66-7ee5-4d6a-b67d-5e7f5d66db15

import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Definitions.Def_FirstPassageLinearTransport_RawClockBudget
import Theorems.Thm_FirstPassageLinearTransport_stageRawClock_le
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_clockGeomLeInvOneSub
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageCount_le
import Theorems.Thm_FirstPassageLinearTransport_stageK_one_le
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
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta omega rawClock : ℝ} (p : StageSetup r eta)
    (homega0 : 0 < omega)
    (hleading : rawClockLeading r eta < rawClock) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      (rawTime n (stageClock p (stageCount omega M) n) : ℝ) <
        rawClock * Real.log n := by
  let gap := rawClock - rawClockLeading r eta
  let A := omega ^ 2 *
    (3 / 2 * Real.logb 2 (stageK p) +
      eta / Real.log 3 * Real.log (stageK p))
  let c := gap * (Real.log 2 / 5)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hlogbK0 : 0 ≤ Real.logb 2 (stageK p) :=
      Real.logb_nonneg (by norm_num) (stageK_one_le p)
    have hlogK0 := Real.log_nonneg (stageK_one_le p)
    have hetaRatio0 : 0 ≤ eta / Real.log 3 :=
      div_nonneg p.eta_pos.le hlog3.le
    exact mul_nonneg (sq_nonneg omega)
      (add_nonneg (mul_nonneg (by norm_num) hlogbK0)
        (mul_nonneg hetaRatio0 hlogK0))
  have hc : 0 < c := by dsimp [c]; positivity
  let q := c / (2 * (A + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hsmallReal := (isLittleO_log_rpow_rpow_atTop
    (s := (1 : ℝ)) 2 (by norm_num)).bound hq
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop (4 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with M hsm hM
  intro n hn hnshell hnboot
  let R := stageCount omega M
  let x : ℝ := (M : ℝ) + 4
  have hx : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxpow0 : 0 ≤ x ^ (1 : ℝ) :=
    Real.rpow_nonneg (zero_le_one.trans hx) _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlogx0 2),
    Real.norm_eq_abs, abs_of_nonneg hxpow0, Real.rpow_one] at hsm
  have herrorScalar : A * (Real.log x) ^ 2 < c * x := by
    have hmul := mul_le_mul_of_nonneg_left hsm (by linarith : 0 ≤ A + 1)
    dsimp [q] at hmul
    have hcoef : A ≤ A + 1 := by linarith
    have hnonneg : 0 ≤ Real.log x ^ (2 : ℕ) := sq_nonneg _
    have hleft : A * Real.log x ^ (2 : ℕ) ≤
        (A + 1) * Real.log x ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hcoef hnonneg
    have hA1ne : A + 1 ≠ 0 := ne_of_gt (by linarith)
    have hhalf : (A + 1) * (c / (2 * (A + 1)) * x) = c / 2 * x := by
      field_simp [hA1ne]
    rw [hhalf] at hmul
    have hmid : A * Real.log x ^ (2 : ℕ) ≤ c / 2 * x :=
      hleft.trans (by simpa [mul_assoc] using hmul)
    have hcx : 0 < c * x := mul_pos hc (zero_lt_one.trans_le hx)
    exact hmid.trans_lt (by
      calc
        c / 2 * x = (c * x) / 2 := by ring
        _ < c * x := div_lt_self hcx (by norm_num))
  have hRle := stageCount_le homega0.le M
  have hR2 : (R : ℝ) ^ 2 ≤ (omega * Real.log x) ^ 2 := by
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    nlinarith
  have hcoef0 : 0 ≤
      3 / 2 * Real.logb 2 (stageK p) +
        eta / Real.log 3 * Real.log (stageK p) := by
    have hlogbK0 : 0 ≤ Real.logb 2 (stageK p) :=
      Real.logb_nonneg (by norm_num) (stageK_one_le p)
    have hlogK0 := Real.log_nonneg (stageK_one_le p)
    have hetaRatio0 : 0 ≤ eta / Real.log 3 :=
      div_nonneg p.eta_pos.le hlog3.le
    exact add_nonneg (mul_nonneg (by norm_num) hlogbK0)
      (mul_nonneg hetaRatio0 hlogK0)
  have herror :
      (R : ℝ) ^ 2 *
          (3 / 2 * Real.logb 2 (stageK p) +
            eta / Real.log 3 * Real.log (stageK p)) <
        gap * (Real.log 2 / 5 * x) := by
    have hmul := mul_le_mul_of_nonneg_right hR2 hcoef0
    have hform : (omega * Real.log x) ^ 2 *
          (3 / 2 * Real.logb 2 (stageK p) +
            eta / Real.log 3 * Real.log (stageK p)) =
        A * (Real.log x) ^ 2 := by
      dsimp [A]
      ring
    rw [hform] at hmul
    exact hmul.trans_lt (by dsimp [c] at herrorScalar; nlinarith)
  have hlogLower : Real.log 2 / 5 * x ≤ Real.log n := by
    have hfrac : x / 5 ≤ (M : ℝ) := by
      dsimp [x]
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hlowerNat : (2 : ℕ) ^ M ≤ n :=
      (mem_dyadicShell.mp hnshell).1
    have hlower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
      have hlowerCast : (2 : ℝ) ^ M ≤ (n : ℝ) := by
        exact_mod_cast hlowerNat
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
        hlowerCast
      rw [Real.log_pow] at h
      exact h
    nlinarith [mul_le_mul_of_nonneg_right hfrac
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
  have hraw := stageRawClock_le p hn hnboot
  have hgeom := clockGeomLeInvOneSub p.r_pos.le p.r_lt_one R
  have hfactor0 : 0 ≤
      3 / (2 * Real.log 2) + eta / Real.log 3 := by
    exact add_nonneg (div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (Real.log_pos (by norm_num)).le))
      (div_nonneg p.eta_pos.le hlog3.le)
  have hlogn0 : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)
  have hlead :
      clockGeom r R *
          (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n ≤
        rawClockLeading r eta * Real.log n := by
    unfold rawClockLeading
    have hm := mul_le_mul_of_nonneg_right hgeom hfactor0
    calc
      clockGeom r R *
            (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n ≤
          ((1 - r)⁻¹ *
            (3 / (2 * Real.log 2) + eta / Real.log 3)) * Real.log n :=
        mul_le_mul_of_nonneg_right hm hlogn0
      _ = (3 / (2 * Real.log 2) + eta / Real.log 3) /
            (1 - r) * Real.log n := by
        rw [div_eq_mul_inv]
        ring
  calc
    (rawTime n (stageClock p R n) : ℝ) ≤
        clockGeom r R *
            (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n +
          (R : ℝ) ^ 2 *
            (3 / 2 * Real.logb 2 (stageK p) +
              eta / Real.log 3 * Real.log (stageK p)) := hraw
    _ < rawClockLeading r eta * Real.log n + gap * Real.log n := by
      apply add_lt_add_of_le_of_lt hlead
      exact herror.trans_le (mul_le_mul_of_nonneg_left hlogLower hgap.le)
    _ = rawClock * Real.log n := by dsimp [gap]; ring
end FirstPassageLinearTransport

-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_quantitativeHeadlineScalars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:47.685878+00:00
-- url     : https://prove2.me/submissions/77b0965a-2493-42d0-a894-6f8a335240a8

import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
import Theorems.Thm_FirstPassageLinearTransport_clockThreshold_lt_one
import Theorems.Thm_FirstPassageLinearTransport_clockThreshold_pos
import Theorems.Thm_FirstPassageLinearTransport_a0_lt_clockThreshold
import Theorems.Thm_FirstPassageLinearTransport_a0_pos
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
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {delta sigma : ℝ}
    (hdelta0 : 0 < delta)
    (hsigma0 : 0 < sigma) (hsigma : sigma < 1 - delta) :
    Nonempty (QuantitativeHeadlineScalars delta sigma) := by
  let r := (a0 + clockThreshold) / 2
  let q := (delta / (1 - sigma) + 1) / 2
  let theta := (delta + q * (1 - sigma)) / 2
  let chi := r ^ (1 / q)
  let omega := theta / Real.log (1 / r)
  let eta := (r - a0) / 2
  have hsigma1 : sigma < 1 := by linarith
  have honeSigma : 0 < 1 - sigma := sub_pos.mpr hsigma1
  have hdeltaGap : delta < 1 - sigma := by linarith
  have hratio0 : 0 < delta / (1 - sigma) :=
    div_pos hdelta0 honeSigma
  have hratio1 : delta / (1 - sigma) < 1 := by
    rw [div_lt_one honeSigma]
    exact hdeltaGap
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hratioq : delta / (1 - sigma) < q := by
    dsimp [q]
    linarith
  have hdeltaq : delta < q * (1 - sigma) := by
    have := mul_lt_mul_of_pos_right hratioq honeSigma
    field_simp [honeSigma.ne'] at this
    simpa [mul_comm] using this
  have htheta0 : 0 < theta := by dsimp [theta]; linarith
  have hdeltatheta : delta < theta := by dsimp [theta]; linarith
  have hthetaq : theta < q * (1 - sigma) := by
    dsimp [theta]
    linarith
  have hr0 : 0 < r := by
    dsimp [r]
    linarith [a0_pos, clockThreshold_pos]
  have ha0r : a0 < r := by
    have hgap : a0 < clockThreshold := by
      simpa [clockThreshold] using a0_lt_clockThreshold
    dsimp [r]
    linarith
  have hrclock : r < clockThreshold := by
    have hgap : a0 < clockThreshold := by
      simpa [clockThreshold] using a0_lt_clockThreshold
    dsimp [r]
    linarith
  have hr1 : r < 1 := hrclock.trans clockThreshold_lt_one
  have honeq : 1 < 1 / q := by
    rw [one_lt_div hq0]
    exact hq1
  have hchi0 : 0 < chi := by
    dsimp [chi]
    exact Real.rpow_pos_of_pos hr0 _
  have hchir : chi < r := by
    dsimp [chi]
    have := Real.rpow_lt_rpow_of_exponent_gt hr0 hr1 honeq
    simpa [Real.rpow_one] using this
  have hchi1 : chi ≤ 1 := hchir.le.trans hr1.le
  have hlogr : 0 < Real.log (1 / r) := by
    exact Real.log_pos (by
      rw [one_div, one_lt_inv₀ hr0]
      exact hr1)
  have homega0 : 0 < omega := by
    dsimp [omega]
    exact div_pos htheta0 hlogr
  have hloginvr : Real.log (1 / r) = -Real.log r := by
    rw [one_div, Real.log_inv]
  have hlogchi : Real.log (1 / chi) = (1 / q) * Real.log (1 / r) := by
    dsimp [chi]
    rw [one_div, Real.log_inv, Real.log_rpow hr0, hloginvr]
    ring
  have hdescent : delta < omega * Real.log (1 / r) := by
    have heq : omega * Real.log (1 / r) = theta := by
      dsimp [omega]
      field_simp [hlogr.ne']
    rw [heq]
    exact hdeltatheta
  have hdensityMargin : omega * Real.log (1 / chi) < 1 - sigma := by
    rw [hlogchi]
    have hqne : q ≠ 0 := hq0.ne'
    have hlogne : Real.log (1 / r) ≠ 0 := hlogr.ne'
    have heq : omega * ((1 / q) * Real.log (1 / r)) = theta / q := by
      dsimp [omega]
      field_simp [hqne, hlogne]
    rw [heq]
    rw [div_lt_iff₀ hq0]
    simpa [mul_comm] using hthetaq
  have hdensity : omega * Real.log (1 / chi) < 1 :=
    hdensityMargin.trans (by linarith)
  have heta0 : 0 < eta := by dsimp [eta]; linarith
  have hetagap : eta < r - a0 := by dsimp [eta]; linarith
  exact ⟨{
    r := r
    chi := chi
    omega := omega
    eta := eta
    a0_lt_r := ha0r
    r_lt_clock := hrclock
    r_lt_one := hr1
    chi_pos := hchi0
    chi_lt_r := hchir
    chi_le_one := hchi1
    omega_pos := homega0
    density_compat := hdensity
    descent_compat := hdescent
    eta_pos := heta0
    eta_gap := hetagap
    density_margin := hdensityMargin }⟩
end FirstPassageLinearTransport

-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_headlineScalars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:00:57.241681+00:00
-- url     : https://prove2.me/submissions/aa70bb9b-459f-4ba4-bfec-e28bc6298b0f

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
theorem _root_.solution {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    Nonempty (HeadlineScalars delta) := by
  let r := (a0 + clockThreshold) / 2
  let q := (delta + 1) / 2
  let chi := r ^ (1 / q)
  let omega := (delta + q) / (2 * Real.log (1 / r))
  let eta := (r - a0) / 2
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
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hdq : delta < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
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
    positivity
  have hloginvr : Real.log (1 / r) = -Real.log r := by
    rw [one_div, Real.log_inv]
  have hlogchi : Real.log (1 / chi) = (1 / q) * Real.log (1 / r) := by
    dsimp [chi]
    rw [one_div, Real.log_inv, Real.log_rpow hr0, hloginvr]
    ring
  have hdescent : delta < omega * Real.log (1 / r) := by
    have heq : omega * Real.log (1 / r) = (delta + q) / 2 := by
      dsimp [omega]
      field_simp [hlogr.ne']
    rw [heq]
    linarith
  have hdensity : omega * Real.log (1 / chi) < 1 := by
    rw [hlogchi]
    have hqne : q ≠ 0 := hq0.ne'
    have hlogne : Real.log (1 / r) ≠ 0 := hlogr.ne'
    have heq : omega * ((1 / q) * Real.log (1 / r)) =
        (delta + q) / (2 * q) := by
      dsimp [omega]
      field_simp [hqne, hlogne]
    rw [heq]
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * q)]
    linarith
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
    eta_gap := hetagap }⟩
end FirstPassageLinearTransport

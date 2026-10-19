-- Prove2me | solution 1 for CohnElkies.tendsto_lowerWallisComplexLogPhase_regularized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/5e61c5f0-8ec8-418b-9eeb-99166eb0cbc8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerWallis_complexEndpointPhase_re
import Theorems.Thm_CohnElkies_lowerWallisComplexLogPhase_ofReal

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (u : ℝ) :
    Tendsto
      (fun n : ℕ =>
        lowerWallisComplexLogPhase
          (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) -
            Complex.I * (u : ℂ)))
      atTop (𝓝 (1 + lowerEndpointPhase (2 * u))) := by
  have hparameter :
      Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ))
        atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases hzero : u = 0
  · subst u
    have hreal :
        Continuous
          (fun a : ℝ =>
            1 + a * Real.log a -
              (a + 1) * Real.log (a + 1)) := by
      have hshift : Continuous (fun a : ℝ => a + 1) := by
        fun_prop
      exact
        (continuous_const.add Real.continuous_mul_log).sub
          (Real.continuous_mul_log.comp hshift)
    have hlimit := hreal.continuousAt.tendsto.comp hparameter
    have hcomputed :
        Tendsto
          (fun n : ℕ =>
            lowerWallisComplexLogPhase
              (((1 / ((n : ℝ) + 1) : ℝ) : ℂ)))
          atTop (𝓝 (1 : ℝ)) := by
      have hrealLimit :
          Tendsto
            (fun n : ℕ =>
              1 + (1 / ((n : ℝ) + 1) : ℝ) *
                  Real.log (1 / ((n : ℝ) + 1)) -
                ((1 / ((n : ℝ) + 1) : ℝ) + 1) *
                  Real.log ((1 / ((n : ℝ) + 1) : ℝ) + 1))
            atTop (𝓝 (1 : ℝ)) := by
        simpa only [Function.comp_apply, zero_mul, mul_zero,
          zero_add, add_zero, one_mul, Real.log_one,
          sub_zero] using! hlimit
      apply hrealLimit.congr'
      filter_upwards [] with n
      exact
        (lowerWallisComplexLogPhase_ofReal
          (show 0 ≤ (1 / ((n : ℝ) + 1) : ℝ) by
            positivity)).symm
    simpa [lowerEndpointPhase] using! hcomputed
  · let z : ℂ := -Complex.I * (u : ℂ)
    have hcast :
        Tendsto
          (fun n : ℕ =>
            ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
          atTop (𝓝 (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hparameter
    have hz :
        Tendsto
          (fun n : ℕ =>
            (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) -
              Complex.I * (u : ℂ)))
          atTop (𝓝 z) := by
      try dsimp [z]
      simpa using!
        hcast.sub (tendsto_const_nhds
          (x := Complex.I * (u : ℂ)))
    have hslit : z ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      right
      try dsimp [z]
      simpa using! hzero
    have hshift : z + 1 ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      try dsimp [z]
      simp
    let w : ℕ → ℂ := fun n =>
      (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) -
        Complex.I * (u : ℂ))
    have hw : Tendsto w atTop (𝓝 z) := by
      exact hz
    have hzlog := hw.clog hslit
    have htranslate := hw.add_const (1 : ℂ)
    have htranslatedLog := htranslate.clog hshift
    have hcomplex :
        Tendsto
          (fun n : ℕ =>
            (1 : ℂ) + w n * Complex.log (w n) -
              (w n + 1) * Complex.log (w n + 1))
          atTop
          (𝓝 ((1 : ℂ) + z * Complex.log z -
            (z + 1) * Complex.log (z + 1))) := by
      exact
        ((tendsto_const_nhds.add (hw.mul hzlog)).sub
          (htranslate.mul htranslatedLog))
    have hreal :
        Tendsto
          (fun n : ℕ => lowerWallisComplexLogPhase (w n))
          atTop (𝓝 (lowerWallisComplexLogPhase z)) := by
      simpa only [lowerWallisComplexLogPhase,
        Function.comp_apply] using!
        (Complex.continuous_re.continuousAt.tendsto.comp hcomplex)
    have hendpoint :
        lowerWallisComplexLogPhase z =
          1 + lowerEndpointPhase (2 * u) := by
      exact lowerWallis_complexEndpointPhase_re u
    rw [hendpoint] at hreal
    exact hreal
end CohnElkies

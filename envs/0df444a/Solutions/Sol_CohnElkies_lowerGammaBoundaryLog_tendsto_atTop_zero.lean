-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_tendsto_atTop_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/b33eb0a5-a35c-4c16-86c8-952cac165ee1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_pole_decomposition

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) :
    Tendsto (lowerGammaBoundaryLog ℓ R)
      (𝓝[≠] (0 : ℝ)) atTop := by
  have hlogbot :
      Tendsto (fun y : ℝ => Real.log (|y| / 2))
        (𝓝[≠] (0 : ℝ)) atBot := by
    have hshift :=
      Real.tendsto_log_nhdsNE_zero.atBot_add
        (tendsto_const_nhds (x := -(Real.log (2 : ℝ))))
    apply hshift.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyzero : y ≠ 0 := by
      simpa using! hy
    rw [Real.log_div
      (abs_ne_zero.mpr hyzero) (by norm_num), Real.log_abs]
    ring
  have hnumPole :
      ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hdenPole :
      ∀ m : ℕ, (ℓ : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hnumGamma :
      ContinuousAt (fun y : ℝ =>
        Complex.Gamma (1 - Complex.I * (y : ℂ) / 2)) 0 := by
    apply (Complex.continuousAt_Gamma (1 : ℂ)
      hnumPole).comp_of_eq
    · fun_prop
    · norm_num
  have hdenGamma :
      ContinuousAt (fun y : ℝ =>
        Complex.Gamma
          ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)) 0 := by
    apply (Complex.continuousAt_Gamma (ℓ : ℂ)
      hdenPole).comp_of_eq
    · fun_prop
    · norm_num
  have hnumLog :
      ContinuousAt (fun y : ℝ =>
        Real.log ‖Complex.Gamma
          (1 - Complex.I * (y : ℂ) / 2)‖) 0 := by
    apply hnumGamma.norm.log
    simp
  have hdenLog :
      ContinuousAt (fun y : ℝ =>
        Real.log ‖Complex.Gamma
          ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) 0 := by
    apply hdenGamma.norm.log
    simpa using! norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero hdenPole)
  have hregular :
      ContinuousAt (fun y : ℝ =>
        ℓ * Real.log (Real.pi * R ^ 2) +
          Real.log ‖Complex.Gamma
            (1 - Complex.I * (y : ℂ) / 2)‖ -
          Real.log ‖Complex.Gamma
            ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) 0 :=
    (continuousAt_const.add hnumLog).sub hdenLog
  have hreglimit :
      Tendsto (fun y : ℝ =>
        ℓ * Real.log (Real.pi * R ^ 2) +
          Real.log ‖Complex.Gamma
            (1 - Complex.I * (y : ℂ) / 2)‖ -
          Real.log ‖Complex.Gamma
            ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (ℓ * Real.log (Real.pi * R ^ 2) +
          Real.log ‖Complex.Gamma (1 : ℂ)‖ -
          Real.log ‖Complex.Gamma (ℓ : ℂ)‖)) := by
    convert! hregular.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ)) using 1;
        norm_num
  have hnegative :
      Tendsto (fun y : ℝ => -Real.log (|y| / 2))
        (𝓝[≠] (0 : ℝ)) atTop :=
    tendsto_neg_atTop_iff.mpr hlogbot
  have hsum := hnegative.atTop_add hreglimit
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyzero : y ≠ 0 := by
    simpa using! hy
  rw [lowerGammaBoundaryLog_pole_decomposition ℓ R hyzero]
  ring
end CohnElkies

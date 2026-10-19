-- Prove2me | solution 1 for CohnElkies.integral_poissonLogistic_mul_lowerWallisPhaseKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/42465ca1-9ac0-4cb7-9f18-556fd651c3bf

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogisticDensity_integrable
import Theorems.Thm_CohnElkies_integral_poissonLogisticDensity
import Theorems.Thm_CohnElkies_poissonLogistic_cosine_transform
import Theorems.Thm_CohnElkies_poissonLogistic_cosine_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ,
      poissonLogisticDensity u * lowerWallisPhaseKernel u t) =
      wallisLaplaceKernel t := by
  have htne : t ≠ 0 := ht.ne'
  have hcos := poissonLogistic_cosine_integrable t
  have hfirst :
      Integrable
        (fun u : ℝ =>
          (1 - Real.exp (-t)) *
            (poissonLogisticDensity u * Real.cos (t * u))) :=
    hcos.const_mul (1 - Real.exp (-t))
  have hsecond :
      Integrable
        (fun u : ℝ =>
          (t * Real.exp (-t)) * poissonLogisticDensity u) :=
    poissonLogisticDensity_integrable.const_mul
      (t * Real.exp (-t))
  calc
    (∫ u : ℝ,
      poissonLogisticDensity u * lowerWallisPhaseKernel u t) =
      ∫ u : ℝ,
        ((1 - Real.exp (-t)) *
            (poissonLogisticDensity u * Real.cos (t * u)) -
          (t * Real.exp (-t)) * poissonLogisticDensity u) /
            t ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold lowerWallisPhaseKernel
      rw [mul_comm u t]
      ring
    _ =
      ((1 - Real.exp (-t)) *
          (∫ u : ℝ,
            poissonLogisticDensity u * Real.cos (t * u)) -
        (t * Real.exp (-t)) *
          (∫ u : ℝ, poissonLogisticDensity u)) /
            t ^ 2 := by
      rw [integral_div,
        integral_sub hfirst hsecond,
        integral_const_mul, integral_const_mul]
    _ =
      ((1 - Real.exp (-t)) * (t / Real.sinh t) -
        t * Real.exp (-t)) / t ^ 2 := by
      rw [poissonLogistic_cosine_transform t,
        if_neg htne, integral_poissonLogisticDensity]
      ring
    _ = wallisLaplaceKernel t := by
      have hsinh : Real.sinh t ≠ 0 :=
        Real.sinh_ne_zero.mpr htne
      have hpositive : Real.exp (-t) ≠ 0 :=
        (Real.exp_pos _).ne'
      have hdiff :
          Real.exp t - Real.exp (-t) ≠ 0 := by
        intro hzero
        apply hsinh
        rw [Real.sinh_eq, hzero]
        norm_num
      have hden : 1 + Real.exp (-t) ≠ 0 := by
        positivity
      rw [Real.sinh_eq]
      have hexp : Real.exp t * Real.exp (-t) = 1 := by
        rw [← Real.exp_add]
        simp
      unfold wallisLaplaceKernel
      field_simp [htne, hpositive, hdiff, hden]; nlinarith [hexp]
end CohnElkies

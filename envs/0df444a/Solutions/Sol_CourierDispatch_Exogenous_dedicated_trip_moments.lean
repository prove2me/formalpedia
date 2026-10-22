-- Prove2me | solution 1 for CourierDispatch.Exogenous.dedicated_trip_moments
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:18:07.572832+00:00
-- url     : https://prove2.me/submissions/106ccb33-d5f7-43d3-9fdf-d510d713b1da

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting
import Definitions.Def_CourierDispatch_Exogenous_DiskLaw

set_option autoImplicit false
open MeasureTheory CourierDispatch.Exogenous

lemma S_disk_moment (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r, ‖x‖ ^ n =
      2 * Real.pi * r ^ (n + 2) / ((n : ℝ) + 2) := by
  have h := MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) ((Set.Iic r).indicator (fun y : ℝ => y ^ n))
  have hL : ∫ x : EuclideanSpace ℝ (Fin 2), (Set.Iic r).indicator (fun y : ℝ => y ^ n) ‖x‖ =
      ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r, ‖x‖ ^ n := by
    rw [← integral_indicator Metric.isClosed_closedBall.measurableSet]
    congr 1
    ext x
    simp [Set.indicator]
  rw [hL] at h
  rw [h]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) = Real.pi := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_two]
    simp [ENNReal.toReal_ofReal Real.pi_pos.le]
  have hint : ∫ y in Set.Ioi (0 : ℝ), y ^ (2 - 1) • (Set.Iic r).indicator (fun y : ℝ => y ^ n) y =
      r ^ (n + 2) / ((n : ℝ) + 2) := by
    have e : ∀ y : ℝ, y ^ (2 - 1) • (Set.Iic r).indicator (fun y : ℝ => y ^ n) y =
        (Set.Iic r).indicator (fun y : ℝ => y ^ (n + 1)) y := by
      intro y
      by_cases hy : y ≤ r
      · simp [Set.indicator, hy, pow_succ]; ring
      · simp [Set.indicator, hy]
    simp_rw [e]
    rw [setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic,
      ← intervalIntegral.integral_of_le hr.le, integral_pow]
    push_cast
    ring
  rw [hdim, hvol, hint]
  simp
  ring

theorem solution (r : ℝ) (hr : 0 < r) :
    MeasureTheory.Integrable (fun x => 2 * ‖x‖) (diskLaw r) ∧
    MeasureTheory.Integrable (fun x => (2 * ‖x‖) ^ 2) (diskLaw r) ∧
    (∫ x, 2 * ‖x‖ ∂(diskLaw r)) = 4 / 3 * r ∧
    (∫ x, (2 * ‖x‖) ^ 2 ∂(diskLaw r)) = 2 * r ^ 2 ∧
    1 / (∫ x, 2 * ‖x‖ ∂(diskLaw r)) = muD r ∧
    1 + ((∫ x, (2 * ‖x‖) ^ 2 ∂(diskLaw r)) - (∫ x, 2 * ‖x‖ ∂(diskLaw r)) ^ 2) /
      (∫ x, 2 * ‖x‖ ∂(diskLaw r)) ^ 2 = CD := by
  set B : Set (EuclideanSpace ℝ (Fin 2)) := Metric.closedBall 0 r with hB
  have hvolB : volume B = ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by
    rw [hB, EuclideanSpace.volume_closedBall_fin_two]
  have hpos : 0 < volume B := by
    rw [hvolB]
    refine ENNReal.mul_pos (pow_ne_zero _ ?_) ?_
    · simpa using hr
    · simpa using Real.pi_pos
  have hfin : volume B ≠ ⊤ := by
    rw [hvolB]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hdl : diskLaw r = (volume B)⁻¹ • volume.restrict B := rfl
  have hct : ((volume B)⁻¹).toReal = 1 / (Real.pi * r ^ 2) := by
    rw [ENNReal.toReal_inv, hvolB, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal Real.pi_pos.le]
    field_simp
  have hcne : (volume B)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hpos.ne'
  have hint1 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin 2) => 2 * ‖x‖) B volume :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall 0 r) (continuous_const.mul continuous_norm).continuousOn
  have hint2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin 2) => (2 * ‖x‖) ^ 2) B volume :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall 0 r) ((continuous_const.mul continuous_norm).pow 2).continuousOn
  have hm1 := S_disk_moment r hr 1
  have hm2 := S_disk_moment r hr 2
  have hE1 : ∫ x, 2 * ‖x‖ ∂(diskLaw r) = 4 / 3 * r := by
    rw [hdl, integral_smul_measure, hct, integral_const_mul]
    have : ∫ x in B, ‖x‖ = 2 * Real.pi * r ^ 3 / 3 := by
      have := hm1
      simp only [pow_one] at this
      rw [this]; push_cast; ring
    rw [this]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hE2 : ∫ x, (2 * ‖x‖) ^ 2 ∂(diskLaw r) = 2 * r ^ 2 := by
    rw [hdl, integral_smul_measure, hct]
    have : ∫ x in B, (2 * ‖x‖) ^ 2 = 4 * (Real.pi * r ^ 4 / 2) := by
      have e : ∀ x : EuclideanSpace ℝ (Fin 2), (2 * ‖x‖) ^ 2 = 4 * ‖x‖ ^ 2 := fun x => by ring
      simp_rw [e]
      rw [integral_const_mul, hm2]
      push_cast
      ring
    rw [this]
    simp only [smul_eq_mul]
    field_simp
    ring
  refine ⟨?_, ?_, hE1, hE2, ?_, ?_⟩
  · rw [hdl]; exact hint1.smul_measure hcne
  · rw [hdl]; exact hint2.smul_measure hcne
  · rw [hE1]; unfold muD; field_simp
  · rw [hE1, hE2]; unfold CD; field_simp; ring

-- Prove2me | solution 1 for DbarRegularity.integral_sphere_two_moments
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T20:35:44.602+00:00
-- url     : https://prove2.me/submissions/55d3049a-514b-41fd-9361-66357c382fb8

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_MeasureTheory_integral_directional_derivative_annulus



namespace DbarRegularity

open MeasureTheory Metric Set

/-- First and second moments of the arc-length measure on the unit circle of `ℝ²`:
`∫ ωᵢ dσ = 0` and `∫ ωᵢ ωⱼ dσ = π δᵢⱼ`. -/
theorem integral_sphere_two_moments :
    (∀ i : Fin 2, ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ω.1 i ∂volume.toSphere = 0) ∧
    (∀ i j : Fin 2, ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ω.1 i * ω.1 j
      ∂volume.toSphere = if i = j then Real.pi else 0) := by
  have h12 : (1 : ℝ) < 2 := by norm_num
  constructor
  · intro i
    have h := MeasureTheory.integral_directional_derivative_annulus (n := 2) (by norm_num)
      (f := fun _ => (1 : ℝ)) (x := 0) one_pos h12
      (fun y _ _ => contDiffAt_const) (EuclideanSpace.single i 1)
    simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, integral_zero,
      one_mul, EuclideanSpace.inner_single_left, map_one] at h
    norm_num at h
    linarith
  · intro i j
    have h := MeasureTheory.integral_directional_derivative_annulus (n := 2) (by norm_num)
      (f := fun y => y j) (x := 0) one_pos h12
      (fun y _ _ => (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.contDiffAt)
      (EuclideanSpace.single i 1)
    have hd : ∀ y : EuclideanSpace ℝ (Fin 2),
        fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => y j) y (EuclideanSpace.single i 1) =
          if i = j then 1 else 0 := by
      intro y
      have := (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).fderiv (x := y)
      change fderiv ℝ (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) y _ = _
      rw [this]
      simp [EuclideanSpace.single_apply, eq_comm]
    simp only [hd, EuclideanSpace.inner_single_left, map_one, one_mul, zero_add] at h
    have hvol : volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) 2 \ closedBall 0 1) =
        3 * Real.pi := by
      rw [measureReal_diff (closedBall_subset_ball h12) measurableSet_closedBall,
        measureReal_def, measureReal_def, EuclideanSpace.volume_ball_fin_two,
        EuclideanSpace.volume_closedBall_fin_two]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal Real.pi_pos.le,
        ENNReal.toReal_ofReal zero_le_one, ENNReal.toReal_ofReal zero_le_two]
      ring
    have hS : ∀ c : ℝ, ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        ((c • ω.1) j) * ω.1 i ∂volume.toSphere =
        c * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ω.1 i * ω.1 j ∂volume.toSphere := by
      intro c
      rw [← integral_const_mul]
      congr 1
      funext ω
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    simp only [hS] at h
    split_ifs with hij
    · rw [if_pos hij, setIntegral_const, smul_eq_mul, mul_one, hvol] at h
      norm_num at h
      linarith
    · rw [if_neg hij, integral_zero] at h
      norm_num at h
      linarith

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set

theorem solution :
    (∀ i : Fin 2, ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ω.1 i ∂volume.toSphere = 0) ∧
    (∀ i j : Fin 2, ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ω.1 i * ω.1 j
      ∂volume.toSphere = if i = j then Real.pi else 0) :=
  integral_sphere_two_moments

-- Prove2me | solution 1 for BlackScholesModel.gaussianReal_exponential_tilt_halfline
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:02:08.593978+00:00
-- url     : https://prove2.me/submissions/d56d0622-0756-4c40-9e3a-8ca18c654cc0

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_gaussianReal_shifted_halfline

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Exponential tilting converts a standard Gaussian into a shifted Gaussian. -/
theorem solution (a y : ℝ) :
    (∫ z in Set.Ioi y, Real.exp (a * z - a ^ 2 / 2)
        ∂(gaussianReal 0 1)) = stdNormalCDF (a - y) ∧
    (∫ z in Set.Iio y, Real.exp (a * z - a ^ 2 / 2)
        ∂(gaussianReal 0 1)) = stdNormalCDF (y - a) := by
  let μ0 : Measure ℝ := gaussianReal 0 1
  let μa : Measure ℝ := gaussianReal a 1
  let f : ℝ → ℝ := fun z => Real.exp (a * z - a ^ 2 / 2)
  have hdensity (z : ℝ) :
      gaussianPDFReal 0 (1 : NNReal) z * f z =
        gaussianPDFReal a (1 : NNReal) z := by
    have h0 :
        gaussianPDFReal 0 (1 : NNReal) z =
          (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-z ^ 2 / 2) := by
      simp [ProbabilityTheory.gaussianPDFReal_def]
    have ha :
        gaussianPDFReal a (1 : NNReal) z =
          (1 / Real.sqrt (2 * Real.pi)) *
            Real.exp (-(z - a) ^ 2 / 2) := by
      simp [ProbabilityTheory.gaussianPDFReal_def]
    dsimp [f]
    rw [h0, ha]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  have hsetIntegral (s : Set ℝ) (hs : MeasurableSet s) :
      (∫ z in s, f z ∂μ0) = μa.real s := by
    have hGaussian0 :
        (∫ z, s.indicator f z ∂μ0) =
        (∫ z, gaussianPDFReal 0 (1 : NNReal) z *
          s.indicator f z ∂volume) := by
      simpa only [smul_eq_mul] using
        (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
          (μ := 0) (v := (1 : NNReal))
          (f := s.indicator f) (by norm_num))
    have hGaussianA :
        (∫ z, s.indicator (fun _ : ℝ => (1 : ℝ)) z ∂μa) =
        (∫ z, gaussianPDFReal a (1 : NNReal) z *
          s.indicator (fun _ : ℝ => (1 : ℝ)) z ∂volume) := by
      simpa only [smul_eq_mul] using
        (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
          (μ := a) (v := (1 : NNReal))
          (f := s.indicator (fun _ : ℝ => (1 : ℝ))) (by norm_num))
    have hPoint (z : ℝ) :
        gaussianPDFReal 0 (1 : NNReal) z * s.indicator f z =
        gaussianPDFReal a (1 : NNReal) z *
          s.indicator (fun _ : ℝ => (1 : ℝ)) z := by
      by_cases hz : z ∈ s
      · simp only [Set.indicator_of_mem hz, mul_one]
        exact hdensity z
      · simp only [Set.indicator_of_notMem hz, mul_zero]
    calc
      (∫ z in s, f z ∂μ0) =
          (∫ z, s.indicator f z ∂μ0) :=
            (MeasureTheory.integral_indicator hs).symm
      _ = (∫ z, gaussianPDFReal 0 (1 : NNReal) z *
          s.indicator f z ∂volume) := hGaussian0
      _ = (∫ z, gaussianPDFReal a (1 : NNReal) z *
          s.indicator (fun _ : ℝ => (1 : ℝ)) z ∂volume) := by
            congr 1
            funext z
            exact hPoint z
      _ = (∫ z, s.indicator (fun _ : ℝ => (1 : ℝ)) z ∂μa) :=
            hGaussianA.symm
      _ = μa.real s := by
            rw [MeasureTheory.integral_indicator_const (1 : ℝ) hs]
            simp
  constructor
  · calc
      (∫ z in Set.Ioi y, Real.exp (a * z - a ^ 2 / 2)
          ∂(gaussianReal 0 1)) =
        μa.real (Set.Ioi y) := hsetIntegral (Set.Ioi y) measurableSet_Ioi
      _ = stdNormalCDF (a - y) :=
        (gaussianReal_shifted_halfline a y).1
  · calc
      (∫ z in Set.Iio y, Real.exp (a * z - a ^ 2 / 2)
          ∂(gaussianReal 0 1)) =
        μa.real (Set.Iio y) := hsetIntegral (Set.Iio y) measurableSet_Iio
      _ = stdNormalCDF (y - a) :=
        (gaussianReal_shifted_halfline a y).2
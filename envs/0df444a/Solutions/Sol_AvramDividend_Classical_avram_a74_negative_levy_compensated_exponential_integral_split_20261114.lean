-- Prove2me | solution 1 for AvramDividend.Classical.avram_a74_negative_levy_compensated_exponential_integral_split_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:16:14.409688+00:00
-- url     : https://prove2.me/submissions/8eca8b59-e066-4496-9a32-e4eb06d1dd68

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a73_negative_mark_compensator_indicator_restrict_integral_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (ν : Measure ℝ) (θ : ℝ)
    (hExp : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) ν)
    (hComp : IntegrableOn
      (fun y : ℝ => y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y)
      (Iio (0 : ℝ)) ν) :
    (∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) ∂ν) =
      (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂ν) -
        θ * (∫ y in Ioo (-1 : ℝ) 0, y ∂ν) := by
  let μ : Measure ℝ := ν.restrict (Iio (0 : ℝ))
  have hExpInt : Integrable (fun y : ℝ => Real.exp (θ * y) - 1) μ :=
    hExp
  have hCompInt :
      Integrable (fun y : ℝ =>
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) μ :=
    hComp
  have hCompScaled :
      Integrable (fun y : ℝ =>
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y)) μ :=
    hCompInt.const_mul θ
  have hPoint (y : ℝ) :
      Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y =
      (Real.exp (θ * y) - 1) -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) := by ring
  have hSplit :
      (∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂ν) =
      (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂ν) -
        θ * (∫ y in Iio (0 : ℝ),
          y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂ν) := by
    change (∫ y, Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂μ) =
        (∫ y, Real.exp (θ * y) - 1 ∂μ) -
          θ * (∫ y,
            y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂μ)
    calc
      (∫ y, Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂μ) =
        (∫ y, (Real.exp (θ * y) - 1) -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) ∂μ) := by
          apply integral_congr_ae
          filter_upwards [] with y
          exact hPoint y
      _ = (∫ y, Real.exp (θ * y) - 1 ∂μ) -
        θ * (∫ y,
          y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂μ) := by
          rw [integral_sub hExpInt hCompScaled, integral_const_mul]
  calc
    (∫ y in Iio (0 : ℝ),
      Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂ν) =
      (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂ν) -
        θ * (∫ y in Iio (0 : ℝ),
          y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂ν) :=
      hSplit
    _ = (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂ν) -
        θ * (∫ y in Ioo (-1 : ℝ) 0, y ∂ν) := by
        rw [avram_a73_negative_mark_compensator_indicator_restrict_integral_20261114 ν]

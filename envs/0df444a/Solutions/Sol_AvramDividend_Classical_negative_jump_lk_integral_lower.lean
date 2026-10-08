-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_lk_integral_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:42:47.013666+00:00
-- url     : https://prove2.me/submissions/2e6168e4-7e10-4d86-b92e-f12b6e4b0945

import Mathlib
import Theorems.Thm_AvramDividend_Classical_negative_jump_lk_integrand_lower

open MeasureTheory Set
open AvramDividend.Classical

theorem solution (ν : Measure ℝ) (θ : ℝ)
    (hfin : ν (Iic (-1 : ℝ)) ≠ ⊤)
    (hint : IntegrableOn
      (fun y : ℝ =>
        Real.exp (θ * y) - 1 -
          θ * y * ((Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y))
      (Iio (0 : ℝ)) ν) :
    -(ν.real (Iic (-1 : ℝ))) ≤
      ∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 -
          θ * y * ((Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y) ∂ν := by
  have hind : IntegrableOn
      (fun y : ℝ =>
        ((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ))) y)
      (Iio (0 : ℝ)) ν := by
    have hi : Integrable
        (fun y : ℝ =>
          ((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ))) y) ν :=
      (integrableOn_const hfin).integrable_indicator measurableSet_Iic
    exact hi.integrableOn
  have hneg : IntegrableOn
      (fun y : ℝ =>
        -((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y))
      (Iio (0 : ℝ)) ν :=
    hind.neg
  have hbound :
      (∫ y in Iio (0 : ℝ),
        -((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y) ∂ν) ≤
      ∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 -
          θ * y * ((Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y) ∂ν := by
    apply setIntegral_mono_on hneg hint measurableSet_Iio
    intro y hy
    have hyneg : y < (0 : ℝ) := by
      simpa only [Set.mem_Iio] using hy
    exact negative_jump_lk_integrand_lower θ y hyneg
  have hindicator :
      (Iio (0 : ℝ)).indicator
        ((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ))) =
      (Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext y
    by_cases hy : y ∈ Iic (-1 : ℝ)
    · have hy0 : y ∈ Iio (0 : ℝ) := by
        have hle : y ≤ (-1 : ℝ) := by
          simpa only [Set.mem_Iic] using hy
        have hylt : y < (0 : ℝ) := by linarith
        simpa only [Set.mem_Iio] using hylt
      simp [Set.indicator, hy, hy0]
    · simp [Set.indicator, hy]
  have hmass :
      (∫ y in Iio (0 : ℝ),
        ((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ))) y ∂ν) =
        ν.real (Iic (-1 : ℝ)) := by
    rw [← integral_indicator measurableSet_Iio]
    rw [hindicator]
    exact integral_indicator_one measurableSet_Iic
  calc
    -(ν.real (Iic (-1 : ℝ))) =
        -(∫ y in Iio (0 : ℝ),
          ((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ))) y ∂ν) := by
          rw [hmass]
    _ = (∫ y in Iio (0 : ℝ),
        -((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y) ∂ν) := by
          rw [integral_neg]
    _ ≤ _ := hbound

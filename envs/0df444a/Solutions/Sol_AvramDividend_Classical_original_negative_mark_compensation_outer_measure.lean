-- Prove2me | solution 1 for AvramDividend.Classical.original_negative_mark_compensation_outer_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:55:58.679913+00:00
-- url     : https://prove2.me/submissions/0a6e0b2d-cf22-4515-8242-6737e3f23709

import Mathlib
import Theorems.Thm_AvramDividend_Classical_original_lk_negative_mark_cutoff_identity
open MeasureTheory Set AvramDividend.Classical

theorem solution (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (θ : ℝ) (hθ : 0 < θ)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (hFn : Integrable
      (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν) :
    (∫ y : ℝ,
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂ν) =
      θ * ((∫ y in Iic (-1 : ℝ), y ∂ν) +
        (∫ y : ℝ, (∫ t in (0 : ℝ)..(-y),
          1 - Real.exp (-θ * t)) ∂ν)) := by
  let L : ℝ → ℝ := (Iic (-1 : ℝ)).indicator (fun y : ℝ => y)
  let F : ℝ → ℝ := fun y => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)
  have hL : Integrable L ν :=
    (integrable_indicator_iff measurableSet_Iic).2 hLarge
  have hF : Integrable F ν := hFn
  have hmark : ∀ᵐ y ∂ν,
      Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y =
          θ * (L y + F y) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hSupp] with y hy
    have hy0 : y < 0 := lt_of_not_ge (by simpa only [mem_Ici] using hy)
    have hp := original_lk_negative_mark_cutoff_identity θ y hθ hy0
    have hLval : L y = if y ≤ -1 then y else 0 := by
      by_cases hh : y ≤ (-1 : ℝ)
      · simp [L, Set.indicator, hh]
      · simp [L, Set.indicator, hh]
    rw [← hLval] at hp
    have hθ0 : θ ≠ 0 := ne_of_gt hθ
    have h := (div_eq_iff hθ0).mp hp
    dsimp [F] at h ⊢
    nlinarith [h]
  have hIntL : (∫ y : ℝ, L y ∂ν) =
      (∫ y in Iic (-1 : ℝ), y ∂ν) := by
    simpa only [L] using (integral_indicator measurableSet_Iic)
  have hIntF : (∫ y : ℝ, F y ∂ν) =
      (∫ y : ℝ, (∫ t in (0 : ℝ)..(-y),
        1 - Real.exp (-θ * t)) ∂ν) := by
    rfl
  have hSum : (∫ y : ℝ, L y + F y ∂ν) =
      (∫ y : ℝ, L y ∂ν) + (∫ y : ℝ, F y ∂ν) :=
    integral_add hL hF
  calc
    _ = (∫ y : ℝ, θ * (L y + F y) ∂ν) := integral_congr_ae hmark
    _ = θ * (∫ y : ℝ, L y + F y ∂ν) := by rw [integral_const_mul]
    _ = θ * ((∫ y : ℝ, L y ∂ν) +
      (∫ y : ℝ, F y ∂ν)) := congrArg (fun z : ℝ => θ * z) hSum
    _ = θ * ((∫ y in Iic (-1 : ℝ), y ∂ν) +
      (∫ y : ℝ, (∫ t in (0 : ℝ)..(-y),
        1 - Real.exp (-θ * t)) ∂ν)) := by rw [hIntL, hIntF]

-- Prove2me | solution 1 for AvramDividend.Classical.bv_laplace_exponent_rearrangement_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T09:19:32.786786+00:00
-- url     : https://prove2.me/submissions/f1405bb5-6f2a-4ee1-a4f7-80fad37929f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation) (θ : ℝ)
    (hexp : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) X.ν)
    (hcomp : IntegrableOn
      (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) X.ν) :
    X.ψ θ = X.drift * θ +
      ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂X.ν := by
  have hind (y : ℝ) :
      θ * y * (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y =
        (Ioo (-1 : ℝ) 1).indicator (fun z : ℝ => θ * z) y := by
    by_cases hy : y ∈ Ioo (-1 : ℝ) 1
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have hind2 (y : ℝ) :
      (Iio (0 : ℝ)).indicator
          (fun z : ℝ =>
            (Ioo (-1 : ℝ) 1).indicator (fun t : ℝ => θ * t) z) y =
        (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => θ * z) y := by
    by_cases h0 : y ∈ Iio (0 : ℝ)
    · by_cases h1 : y ∈ Ioo (-1 : ℝ) 1
      · have hs : y ∈ Ioo (-1 : ℝ) 0 := ⟨h1.1, h0⟩
        simp [Set.indicator_of_mem h0, Set.indicator_of_mem h1,
          Set.indicator_of_mem hs]
      · have hs : y ∉ Ioo (-1 : ℝ) 0 := by
          intro h
          apply h1
          exact ⟨h.1, lt_trans h.2 (by norm_num)⟩
        simp [Set.indicator_of_mem h0,
          Set.indicator_of_notMem h1, Set.indicator_of_notMem hs]
    · have hs : y ∉ Ioo (-1 : ℝ) 0 := by
        intro h
        exact h0 h.2
      simp [Set.indicator_of_notMem h0, Set.indicator_of_notMem hs]
  have hcomp_int :
      (∫ y in Iio (0 : ℝ),
          θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y ∂X.ν) =
        θ * (∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν) := by
    calc
      (∫ y in Iio (0 : ℝ),
          θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y ∂X.ν) =
          ∫ y : ℝ,
            (Iio (0 : ℝ)).indicator
              (fun z : ℝ =>
                (Ioo (-1 : ℝ) 1).indicator
                  (fun t : ℝ => θ * t) z) y ∂X.ν := by
            simp_rw [hind]
            rw [integral_indicator measurableSet_Iio]
      _ = ∫ y : ℝ,
          (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => θ * z) y ∂X.ν := by
            congr 1
            funext y
            exact hind2 y
      _ = ∫ y in Ioo (-1 : ℝ) 0, θ * y ∂X.ν :=
        integral_indicator measurableSet_Ioo
      _ = θ * (∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν) := by
        rw [integral_const_mul]
  have hmain :
      (∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1 -
            θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂X.ν) =
        (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂X.ν) -
          θ * (∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν) := by
    rw [integral_sub hexp hcomp, hcomp_int]
  change X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
    (∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂X.ν) =
    (X.c - ∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν) * θ +
      (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂X.ν)
  rw [hbv.1, hmain]
  ring

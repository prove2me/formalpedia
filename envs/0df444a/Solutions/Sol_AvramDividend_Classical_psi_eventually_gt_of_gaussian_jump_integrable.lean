-- Prove2me | solution 1 for AvramDividend.Classical.psi_eventually_gt_of_gaussian_jump_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:16:10.385556+00:00
-- url     : https://prove2.me/submissions/f55e3a5e-13dd-42f0-a8b6-e7889211ac5e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_lk_integral_lower
import Theorems.Thm_AvramDividend_Classical_eventually_quadratic_lower_gt

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hσ : 0 < X.σ)
    (hν : X.ν (Iic (-1 : ℝ)) ≠ ⊤)
    (hjump : ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn
        (fun y : ℝ => Real.exp (θ * y) - 1 -
          θ * y * ((Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y))
        (Iio (0 : ℝ)) X.ν) :
    ∃ β0 : ℝ, 0 ≤ β0 ∧
      ∀ θ : ℝ, β0 ≤ θ → q < X.ψ θ := by
  have hA : 0 < X.σ ^ 2 / 2 := by positivity
  obtain ⟨β0, hβ0, hpoly⟩ :=
    eventually_quadratic_lower_gt
      (X.σ ^ 2 / 2) X.c (X.ν.real (Iic (-1 : ℝ))) q hA
  refine ⟨β0, hβ0, ?_⟩
  intro θ hθ
  have hθ0 : 0 ≤ θ := hβ0.trans hθ
  have hkernel :=
    negative_jump_lk_integral_lower
      X.ν θ hν (hjump θ hθ0)
  have hgrowth := hpoly θ hθ
  have hkernel' :
      -X.ν.real (Iic (-1 : ℝ)) ≤
        ∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 -
          θ * y * ((Ioo (-1 : ℝ) 1).indicator
            (1 : ℝ → ℝ) y) ∂X.ν := by
    simpa only
      [show (1 : ℝ → ℝ) = (fun _ : ℝ => (1 : ℝ)) from rfl]
      using hkernel
  dsimp [SpectrallyNegativeLevy.ψ, laplaceExponent]
  nlinarith only [hkernel', hgrowth]

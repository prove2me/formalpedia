-- Prove2me | solution 1 for AvramDividend.Classical.psi_eventually_gt_of_gaussian_levy_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:18:51.210095+00:00
-- url     : https://prove2.me/submissions/585d2f59-7595-4a6d-89b4-aaefadea9dd1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_large_negative_jump_mass
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian_jump_integrable

open MeasureTheory Set
open scoped ENNReal NNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hσ : 0 < X.σ)
    (hjump : ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn (fun y : ℝ =>
        Real.exp (θ * y) - 1 -
          θ * y * ((Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y))
        (Iio (0 : ℝ)) X.ν) :
    ∃ β0 : ℝ, 0 ≤ β0 ∧
      ∀ θ : ℝ, β0 ≤ θ → q < X.ψ θ := by
  have hν : X.ν (Iic (-1 : ℝ)) ≠ ⊤ :=
    finite_large_negative_jump_mass X.ν X.ν_integrable
  exact psi_eventually_gt_of_gaussian_jump_integrable
    X q hσ hν hjump

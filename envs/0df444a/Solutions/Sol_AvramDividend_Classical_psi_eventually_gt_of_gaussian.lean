-- Prove2me | solution 1 for AvramDividend.Classical.psi_eventually_gt_of_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T17:45:26.614793+00:00
-- url     : https://prove2.me/submissions/ecc9c3e4-cd0a-4025-a762-0a842ff96342

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian_levy_integrable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hσ : 0 < X.σ) :
    ∃ β0 : ℝ, 0 ≤ β0 ∧
      ∀ θ : ℝ, β0 ≤ θ → q < X.ψ θ := by
  have hjump : ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn
        (fun y : ℝ =>
          Real.exp (θ * y) - 1 -
            θ * y * ((Ioo (-1 : ℝ) 1).indicator
              (fun _ : ℝ => (1 : ℝ)) y))
        (Iio (0 : ℝ)) X.ν := by
    intro θ hθ
    exact levy_compensated_jump_integrable_nonneg X θ hθ
  exact psi_eventually_gt_of_gaussian_levy_integrable X q hσ hjump

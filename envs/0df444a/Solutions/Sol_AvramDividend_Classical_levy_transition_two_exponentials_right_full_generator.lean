-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_two_exponentials_right_full_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:08:50.799486+00:00
-- url     : https://prove2.me/submissions/aa2b48d5-d398-4efd-8524-74d4eae06117

import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_two_exponentials_right_generator
import Theorems.Thm_AvramDividend_Classical_levy_generator_two_exponentials_linear
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Compose the proved two-term semigroup slope and full generator linearity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b θ φ x : ℝ) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, (a * Real.exp (θ * (x + X.X (Real.toNNReal h) ω)) +
                 b * Real.exp (φ * (x + X.X (Real.toNNReal h) ω))) ∂P) -
          (a * Real.exp (θ * x) + b * Real.exp (φ * x))))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator
        (fun z : ℝ => a * Real.exp (θ * z) + b * Real.exp (φ * z)) x)) := by
  have hgen := (levy_generator_two_exponentials_linear X a b θ φ x hθ hφ).2
  rw [hgen]
  exact levy_transition_two_exponentials_right_generator X a b θ φ x hθ hφ

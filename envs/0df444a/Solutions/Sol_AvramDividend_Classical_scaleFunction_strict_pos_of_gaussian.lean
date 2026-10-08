-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_strict_pos_of_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T17:48:33.425676+00:00
-- url     : https://prove2.me/submissions/1ced0cbb-0376-4fda-ab07-2d022b5f8176

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_eventually_positive_quadratic_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_eventual_psi_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (a : ℝ) (ha : 0 < a) :
    0 < W a := by
  obtain ⟨β, C, hβ, hC, hbound⟩ :=
    psi_eventually_positive_quadratic_of_gaussian X q hσ
  have hψ : ∀ θ : ℝ, β ≤ θ → q < X.ψ θ := by
    intro θ hθ
    exact (hbound θ hθ).1
  have hquadratic : ∀ θ : ℝ, β ≤ θ →
      X.ψ θ - q ≤ C * (1 + θ ^ 2) := by
    intro θ hθ
    exact (hbound θ hθ).2
  exact (scaleFunction_strict_pos_of_eventual_psi_bound
    X q W hW β C hβ hψ hquadratic) a ha

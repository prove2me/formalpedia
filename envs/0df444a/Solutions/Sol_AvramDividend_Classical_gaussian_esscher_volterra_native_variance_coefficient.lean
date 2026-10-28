-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_volterra_native_variance_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:48:45.829079+00:00
-- url     : https://prove2.me/submissions/18f1f0d5-5c24-47f8-917d-6decf2c557d3

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_native_levy_esscher_double_tail_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_canonical_volterra_identity_of_positive_sigma
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ∃ (β : ℝ) (K : ℝ → ℝ),
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      ∀ x : ℝ, 0 < x →
        (X.σ ^ 2 / 2) * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x :=
  ⟨_, _, AvramDividend.Classical.gaussian_native_levy_esscher_double_tail_integrable X φ hφ,
    AvramDividend.Classical.gaussian_esscher_canonical_volterra_identity_of_positive_sigma X q hq W hW
      hσ φ hφ hroot V hV _ _ _ rfl rfl rfl⟩

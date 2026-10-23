-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_integrated_volterra_of_positive_sigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:17:38.700064+00:00
-- url     : https://prove2.me/submissions/52f0f4e6-721b-4c4c-954b-a39e617075e2

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_kernel_equation_of_positive_sigma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Separate the exact Gaussian Volterra identity from the elementary local bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ (a β : ℝ) (K : ℝ → ℝ),
      0 < a ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x) := by
  obtain ⟨a, β, K, ha, hK, hEq⟩ :=
    gaussian_esscher_volterra_kernel_equation_of_positive_sigma
      X q hq W hW hσ φ hφ hroot V hV
  refine ⟨a, β, K, ha, hK, ?_, hEq⟩
  exact gaussian_esscher_tilted_scale_locally_bounded
    X q hq W hW hσ φ hφ V hV

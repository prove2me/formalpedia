-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:28:27.950272+00:00
-- url     : https://prove2.me/submissions/cda3fac9-06f0-4000-b111-f15b6f929377

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_curvature_zeroext_weighted
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_gaussian_compensated_kernel_product_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Absolute Fubini product integrability for the original Gaussian
    compensated Lévy generator and its genuine q-scale at all large weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      Integrable
        (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod
          (X.ν.restrict (Iio (0 : ℝ)))) := by
  obtain ⟨b, hb⟩ :=
    avram_wave3_05_source_gaussian_curvature_zeroext_weighted
      X hX q hq W hW hσ φ hφ hroot
  let F : ℝ → ℝ :=
    (Ioi (0 : ℝ)).piecewise (deriv (deriv W)) (fun _ => 0)
  have hFpoint : ∀ u : ℝ, 0 < u → F u = iteratedDeriv 2 W u := by
    intro u hu
    have hmem : u ∈ Ioi (0 : ℝ) := hu
    simp [F, Set.piecewise, hmem, iteratedDeriv_succ, iteratedDeriv_one]
  refine ⟨b, ?_⟩
  intro θ hθb hθ hqθ
  have hdata := hb θ hθb hθ hqθ
  change Measurable F ∧ ContinuousOn F (Ioi (0 : ℝ)) ∧
    Integrable (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume at hdata
  obtain ⟨hFm, hFc, hFi⟩ := hdata
  exact avram_wave4_05_source_gaussian_compensated_kernel_product_integrable
    X hX q hq W hW hσ F hFpoint hFc hFm θ hθ hqθ hFi

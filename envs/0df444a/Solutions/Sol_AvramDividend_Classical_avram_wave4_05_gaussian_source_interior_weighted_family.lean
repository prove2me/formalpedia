-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_source_interior_weighted_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:41:17.198593+00:00
-- url     : https://prove2.me/submissions/2d2f48d6-5b03-485e-9b0a-c28e62dcebac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_curvature_zeroext_weighted
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_interior_generator_weighted_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual Gaussian q-scale function supplies all analytic premises for
    the interior compensated-jump weighted quadratic bound at every sufficiently
    large admissible Laplace parameter. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      ∀ r : ℝ, 0 < r → r < 1 →
        let F : ℝ → ℝ :=
          (Ioi (0 : ℝ)).piecewise (deriv (deriv W)) (fun _ => 0)
        IntegrableOn
          (fun x : ℝ => Real.exp (-θ * x) *
            |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|)
          (Ioi r) volume ∧
        (∫ x in Ioi r, Real.exp (-θ * x) *
          |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) ≤
          (r ^ 2 / 2) *
            (∫ u : ℝ, Real.exp (-θ * u) * |F u|) := by
  obtain ⟨b, hb⟩ :=
    avram_wave3_05_source_gaussian_curvature_zeroext_weighted
      X hX q hq W hW hσ φ hφ hroot
  have hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
  let F : ℝ → ℝ :=
    (Ioi (0 : ℝ)).piecewise (deriv (deriv W)) (fun _ => 0)
  have hFpoint : ∀ u : ℝ, 0 < u → F u = iteratedDeriv 2 W u := by
    intro u hu
    have hmem : u ∈ Ioi (0 : ℝ) := hu
    simp [F, Set.piecewise, hmem, iteratedDeriv_succ, iteratedDeriv_one]
  refine ⟨b, ?_⟩
  intro θ hθb hθ hqθ r hr hr1
  have hdata := hb θ hθb hθ hqθ
  change Measurable F ∧ ContinuousOn F (Ioi (0 : ℝ)) ∧
    Integrable (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume at hdata
  obtain ⟨hFm, hFc, hFi⟩ := hdata
  exact avram_wave4_05_source_interior_generator_weighted_quadratic
    W F hC2 hFpoint r θ hr hr1 hθ hFc hFm hFi

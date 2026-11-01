-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_source_harmonic_from_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:25:38.68676+00:00
-- url     : https://prove2.me/submissions/58c228fa-215e-4fac-bc62-76e133cfd068

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_generator_from_eventual_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Eventual residual transforms determine the genuine source q-harmonic generator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hres : ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x : ℝ, 0 < x →
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by
  obtain ⟨b, hb⟩ := hres
  obtain ⟨β₀, hβ₀, hψ⟩ := psi_eventually_gt_of_gaussian X q hσ
  apply avram_wave3_05_gaussian_generator_from_eventual_laplace
    X hX q hq W hW hσ (max b β₀)
  intro θ hθ
  have hbθ : b ≤ θ :=
    le_trans (le_max_left b β₀) (le_of_lt hθ)
  have hβθ : β₀ ≤ θ :=
    le_trans (le_max_right b β₀) (le_of_lt hθ)
  exact hb θ hbθ (le_trans hβ₀ hβθ) (hψ θ hβθ)

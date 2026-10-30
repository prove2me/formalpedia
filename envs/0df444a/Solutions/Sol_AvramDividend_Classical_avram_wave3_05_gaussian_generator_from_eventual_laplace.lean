-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_gaussian_generator_from_eventual_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:04:04.963202+00:00
-- url     : https://prove2.me/submissions/38c1285e-061a-4212-a402-2c0ccfae14da

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_sigma_pos
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_zero_origin_C2
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing
import Theorems.Thm_AvramDividend_Classical_generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original Gaussian scale generator is q-harmonic when its residual
    transform vanishes on one terminal half-line of Laplace parameters. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (b : ℝ)
    (hweighted : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x : ℝ, 0 < x →
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by
  have hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiffOn_two_of_sigma_pos X hX q hq W hW hσ
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hcont : ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioi (0 : ℝ)) :=
    generator_residual_continuousOn_Ioi_of_zero_origin_C2 X q W hW hzero hC2
  intro x hx
  have ha : 0 < x + 1 := by linarith
  have hxa : x ∈ Ioo (0 : ℝ) (x + 1) := ⟨hx, by linarith⟩
  have hsub : Ioo (0 : ℝ) (x + 1) ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact hy.1
  have hae := scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing
    X q W hW (x + 1) ha b hcont hweighted
  have hpt := generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
    X q W (x + 1) (hcont.mono hsub) hae x hxa
  exact ⟨scaleFunction_generatorIntegrable_of_contDiff_two
    X q W hW (x + 1) x hxa (hC2.mono hsub), hpt⟩

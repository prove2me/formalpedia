-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_full_halfline_jump_fubini_of_slice_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:27:14.645725+00:00
-- url     : https://prove2.me/submissions/7a592336-19bf-471e-b53c-c57be4a6867d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_integrable_prod_of_slice_norm_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_weighted_global_fubini_of_prod_integrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The quadratic Lévy moment dominates slice norms, yielding global Fubini. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ C : ℝ)
    (hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))))
    (hsections : ∀ᵐ y ∂(X.ν.restrict (Iio (0 : ℝ))),
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        SpectrallyNegativeLevy.generatorIntegrand W x y) (Ioi (0 : ℝ)))
    (hnorm_meas : AEStronglyMeasurable
      (fun y : ℝ => ∫ x in Ioi (0 : ℝ),
        ‖Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y‖)
      (X.ν.restrict (Iio (0 : ℝ))))
    (hdom : ∀ᵐ y ∂(X.ν.restrict (Iio (0 : ℝ))),
      (∫ x in Ioi (0 : ℝ),
        ‖Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y‖)
        ≤ C * min 1 (y ^ 2)) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let ν₀ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : SFinite ν₀ := levy_negative_jump_measure_sFinite X
  have hmin_meas :
      AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards with y
    positivity
  have hminfull : Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hmin_meas hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hmin : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν₀ :=
    hminfull.mono_measure Measure.restrict_le_self
  have hprod : Integrable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      (μ.prod ν₀) := by
    exact integrable_prod_of_slice_norm_quadratic_bound
      μ ν₀ _ C hmeas hsections hnorm_meas hmin hdom
  exact scaleFunction_generator_weighted_global_fubini_of_prod_integrable
    X W θ hprod

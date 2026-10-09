-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_full_halfline_jump_fubini_of_weighted_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:12:25.025334+00:00
-- url     : https://prove2.me/submissions/760349b3-5356-49a7-b3a1-04f067c9676f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_integrable_prod_of_factorized_bound
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ : ℝ) (g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioi (0 : ℝ)))
    (hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))))
    (hdom : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))),
      ‖Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2‖ ≤
        |g p.1| * |min (1 : ℝ) (p.2 ^ 2)|) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y)
      ∂X.ν := by
  letI : SFinite (X.ν.restrict (Iio 0)) :=
    levy_negative_jump_measure_sFinite X
  have hmin_meas :
      AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards with y
    positivity
  have hminfull :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hmin_meas hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hmin :
      Integrable (fun y : ℝ => min 1 (y ^ 2))
        (X.ν.restrict (Iio 0)) :=
    hminfull.mono_measure Measure.restrict_le_self
  have hprod : Integrable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) :=
    integrable_prod_of_factorized_bound
      (volume.restrict (Ioi (0 : ℝ)))
      (X.ν.restrict (Iio (0 : ℝ)))
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      g (fun y => min 1 (y ^ 2)) hg hmin hmeas hdom
  calc
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ x in Ioi (0 : ℝ),
        (∫ y in Iio (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [integral_const_mul]
    _ = ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y)
      ∂X.ν := integral_integral_swap hprod

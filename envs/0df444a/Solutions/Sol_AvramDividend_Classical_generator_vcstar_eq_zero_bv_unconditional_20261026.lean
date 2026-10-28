-- Prove2me | solution 1 for AvramDividend.Classical.generator_vcstar_eq_zero_bv_unconditional_20261026
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:55:49.384821+00:00
-- url     : https://prove2.me/submissions/3635a8d2-ce21-48b3-8964-4db93547a084

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_of_zero_scale_factor
import Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Both the zero-normalisation and nonzero-normalisation BV branches. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x = 0 := by
  intro x hx
  have ha : 0 < (cstar W).toReal := lt_trans hx.1 hx.2
  by_cases hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) = 0
  · exact (generator_vcstar_eq_zero_of_zero_scale_factor X q W hW.1 hk) x hx
  · exact (vcstar_interior_harmonicity_of_scale_harmonicity X q W hW ha
      (scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
        X hX hbv q hq W hW hc hk
        (bv_weighted_generator_residual_family_from_scale_20261026
          X hX hbv q hq W hW))) x hx

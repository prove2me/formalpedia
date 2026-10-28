-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_q_harmonic_bv_unconditional_20261026
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:51:39.802447+00:00
-- url     : https://prove2.me/submissions/a9a8b528-cf5e-40ec-9d78-75b3629dc09d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Unconditional BV q-scale generator harmonicity below the barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by
  exact scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
    X hX hbv q hq W hW hc hk
    (bv_weighted_generator_residual_family_from_scale_20261026
      X hX hbv q hq W hW)

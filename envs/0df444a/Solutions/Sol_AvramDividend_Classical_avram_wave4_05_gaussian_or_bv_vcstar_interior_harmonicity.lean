-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_vcstar_interior_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:41:48.162042+00:00
-- url     : https://prove2.me/submissions/1bee4494-28bc-4800-b6af-556b4ae48c60

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_vcstar_interior_harmonicity
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_bv_unconditional_20261026

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The two solved original-source cases imply interior generator harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation)
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by
  rcases hbranch with hσ | hbv
  · exact avram_wave4_05_gaussian_vcstar_interior_harmonicity
      X hX q hq W hW hσ hc
  · exact generator_vcstar_eq_zero_bv_unconditional_20261026
      X hX hbv q hq W hW hc

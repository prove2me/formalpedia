-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_signed_generator_residual_le_band_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:25:55.443602+00:00
-- url     : https://prove2.me/submissions/43889cec-c76b-4bee-b03f-a659ad1a4e61

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_signed_generator_residual_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_overshoot_integral_le_band_mass_of_levy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A fully quantitative source Lévy generator inequality with two finite
measures: the positive small-ruin overshoot strip and negative large-ruin
killing intensity, without extra moment assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤
        X.c + (X.ν).real (Ioo (-1 : ℝ) (-x)) *
          max 0 (1 - vcstar W x) -
        (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x -
        q * vcstar W x := by
  have h0 : 0 < x := lt_of_le_of_lt ENNReal.toReal_nonneg hx
  obtain ⟨hdom, hres⟩ :=
    avram_wave4_05_source_signed_generator_residual_bound
      X hX q hq W hW x hx
  have hband :=
    avram_wave4_05_source_ruin_overshoot_integral_le_band_mass_of_levy
      X W x h0
  refine ⟨hdom, ?_⟩
  linarith

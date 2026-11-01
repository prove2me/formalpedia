-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_vcstar_hjb_all_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:41:50.423894+00:00
-- url     : https://prove2.me/submissions/8b316cd4-359c-4e30-b7ee-1131986d3ef3

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_hjb_all_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The two canonically solved Lévy branches satisfy the exact source HJB. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  rcases hbranch with hσ | hbv
  · exact avram_wave4_05_gaussian_vcstar_hjb_all_positive_of_generator
      X hX q hq W hW hσ hgen
  · exact avram_ws01e_bf_new_bv_hjb_all_positive
      X hX q hq W hW hbv hgen

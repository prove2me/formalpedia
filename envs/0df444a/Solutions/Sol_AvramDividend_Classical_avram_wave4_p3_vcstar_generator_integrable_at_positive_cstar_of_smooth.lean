-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_vcstar_generator_integrable_at_positive_cstar_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:02:15.985489+00:00
-- url     : https://prove2.me/submissions/9e60abc0-f893-4856-8bce-3e1d8d5e4ca1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_vcstar_generator_integrable_at_positive_cap_of_global_C2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Source generator-domain membership at the cap for each original smoothness case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal := by
  have ha : 0 < (cstar W).toReal := ENNReal.toReal_pos hcpos.ne' hc.ne
  rcases h_smooth with hσ | hbv | hC2
  · exact (vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
      X hX q hq W hW hc hcpos (Or.inl hσ)).1
  · exact (vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
      X hX q hq W hW hc hcpos (Or.inr hbv)).1
  · exact
      avram_wave4_05a_vcstar_generator_integrable_at_positive_cap_of_global_C2
        X q W hW ha hC2

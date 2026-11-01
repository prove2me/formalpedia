-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_vcstar_hjb_all_positive_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:45:14.253206+00:00
-- url     : https://prove2.me/submissions/3ffc3ba5-6791-4888-ba62-6baf2b1566f3

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_residual_from_eventual_product
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_harmonic_from_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_hjb_from_source_scale_harmonicity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Original Gaussian generator's full HJB for the barrier candidate from source data. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  obtain ⟨φ, hφ, hroot⟩ :=
    avram_wave4_05_source_positive_psi_root_of_standing X hX q hq
  have hprod :=
    avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
      X hX q hq W hW hσ φ hφ hroot
  have hres :=
    avram_wave4_05_gaussian_residual_from_eventual_product
      X hX q hq W hW hσ φ hφ hroot hprod
  have hscale :=
    avram_wave4_05_gaussian_source_harmonic_from_residual
      X hX q hq W hW hσ hres
  exact avram_wave4_05_gaussian_hjb_from_source_scale_harmonicity
    X hX q hq W hW hσ hscale hgen

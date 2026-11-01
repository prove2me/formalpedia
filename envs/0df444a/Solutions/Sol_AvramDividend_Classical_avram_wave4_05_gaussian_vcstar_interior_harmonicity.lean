-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_vcstar_interior_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:37:48.914896+00:00
-- url     : https://prove2.me/submissions/ce6f07d1-6df2-45f2-8278-a55d7322d855

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_residual_from_eventual_product
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_harmonic_from_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_scale_to_vcstar
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- The original Gaussian generator annihilates the actual optimal-barrier candidate. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by
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
  exact avram_wave4_05_source_scale_to_vcstar
    X hX q hq W hW hc hscale

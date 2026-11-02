-- Prove2me | solution 4 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_generatorIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:37:18.003195+00:00
-- url     : https://prove2.me/submissions/0d022f98-0483-4380-80a4-4680b5434ef8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_scale_generator_harmonic_on_all_positive_reserves_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_of_notBV
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_residual_from_eventual_product
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_harmonic_from_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a))
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by
  intro x hx
  by_cases hbv : X.BoundedVariation
  · exact (bv_scale_generator_harmonic_on_all_positive_reserves_ws01b
      X hX hbv q hq W hW x hx.1).2
  · by_cases hzero : X.σ = 0
    · have hC2 : ContDiffOn ℝ 2 W (Ioo 0 a) := by
        rcases h_smooth with hpos | hbounded | hC2
        · exact ((ne_of_gt hpos) hzero).elim
        · exact (hbv hbounded).elim
        · exact hC2
      exact (avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
        X hX hzero hbv q hq W hW a ha hC2 x hx).2
    · have hσ : 0 < X.σ :=
        lt_of_le_of_ne X.σ_nonneg (Ne.symm hzero)
      obtain ⟨φ, hφ, hroot⟩ :=
        unbounded_esscher_root_of_notBV X q hq hbv
      have hproduct :=
        avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
          X hX q hq W hW hσ φ hφ hroot
      have hres :=
        avram_wave4_05_gaussian_residual_from_eventual_product
          X hX q hq W hW hσ φ hφ hroot hproduct
      exact (avram_wave4_05_gaussian_source_harmonic_from_residual
        X hX q hq W hW hσ hres x hx.1).2

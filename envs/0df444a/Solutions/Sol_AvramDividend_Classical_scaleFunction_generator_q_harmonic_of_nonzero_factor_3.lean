-- Prove2me | solution 3 for AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:04:18.29525+00:00
-- url     : https://prove2.me/submissions/517c283f-5897-46a1-b31e-b6148aa08a61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_residual_from_eventual_product
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_harmonic_from_residual
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_vcstar_nonzero
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Original source non-Gaussian, Gaussian and BV generator harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by
  by_cases hσpos : 0 < X.σ
  · obtain ⟨φ, hφ, hroot⟩ :=
      avram_wave4_05_source_positive_psi_root_of_standing X hX q hq
    have hprod :=
      avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
        X hX q hq W hW hσpos φ hφ hroot
    have hres :=
      avram_wave4_05_gaussian_residual_from_eventual_product
        X hX q hq W hW hσpos φ hφ hroot hprod
    have hscale :=
      avram_wave4_05_gaussian_source_harmonic_from_residual
        X hX q hq W hW hσpos hres
    exact fun x hx => hscale x hx.1
  by_cases hbv : X.BoundedVariation
  · exact
      scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
        X hX hbv q hq W hW hc hk
        (bv_weighted_generator_residual_family_from_scale_20261026
          X hX hbv q hq W hW)
  have hC2 : ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) := by
    apply scaleFunction_contDiffOn_two_of_vcstar_nonzero W _ hk
    rcases h_smooth with hσ | hbv' | hvc
    · exact False.elim (hσpos hσ)
    · exact False.elim (hbv hbv')
    · exact hvc
  have hσ0 : X.σ = 0 :=
    le_antisymm (le_of_not_gt hσpos) X.σ_nonneg
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hc)
      (ne_of_lt (cstar_lt_top X hX q hq W hW))
  exact avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
    X hX hσ0 hbv q hq W hW (cstar W).toReal ha hC2

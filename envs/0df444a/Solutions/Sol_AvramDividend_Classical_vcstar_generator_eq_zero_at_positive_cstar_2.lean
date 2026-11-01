-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_generator_eq_zero_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:25:59.162624+00:00
-- url     : https://prove2.me/submissions/1b64a31c-5077-4015-a5cd-3dacde71b07b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_standing_nonzero_scale_normaliser
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_residual_from_eventual_product
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_harmonic_from_residual
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_vcstar_nonzero
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
import Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_interior_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hsmooth_copy := h_smooth
  have hsmooth_inner :
      0 < X.σ ∨ X.BoundedVariation ∨
        ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal) := by
    rcases hsmooth_copy with hσ | hbv | hC2
    · exact Or.inl hσ
    · exact Or.inr (Or.inl hbv)
    · exact Or.inr (Or.inr (hC2.mono (by intro z hz; exact hz.1)))
  have hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 :=
    avram_wave4_05_standing_nonzero_scale_normaliser X hX q hq W hW hcpos
  have hscale : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by
    intro x hx
    by_cases hσ : 0 < X.σ
    · obtain ⟨φ, hφ, hroot⟩ :=
        avram_wave4_05_source_positive_psi_root_of_standing X hX q hq
      have hprod :=
        avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
          X hX q hq W hW hσ φ hφ hroot
      have hres :=
        avram_wave4_05_gaussian_residual_from_eventual_product
          X hX q hq W hW hσ φ hφ hroot hprod
      exact (avram_wave4_05_gaussian_source_harmonic_from_residual
        X hX q hq W hW hσ hres) x hx.1
    · by_cases hbv : X.BoundedVariation
      · exact (scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
          X hX hbv q hq W hW hcpos hk
          (bv_weighted_generator_residual_family_from_scale_20261026
            X hX hbv q hq W hW)) x hx
      · have hC2vc : ContDiffOn ℝ 2 (vcstar W)
            (Ioo 0 (cstar W).toReal) := by
          rcases hsmooth_inner with hpos | hBV | hC2
          · exact (hσ hpos).elim
          · exact (hbv hBV).elim
          · exact hC2
        have hWc2 :=
          scaleFunction_contDiffOn_two_of_vcstar_nonzero W hC2vc hk
        have hσ0 : X.σ = 0 :=
          le_antisymm (le_of_not_gt hσ) X.σ_nonneg
        exact (avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
          X hX hσ0 hbv q hq W hW (cstar W).toReal ha hWc2) x hx
  have hinside :=
    vcstar_interior_harmonicity_of_scale_harmonicity X q W hW ha hscale
  exact avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_interior_eq
    X hX q hq W hW hc hcpos h_smooth (fun x hx => (hinside x hx).2)

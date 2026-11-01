-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:19:20.706629+00:00
-- url     : https://prove2.me/submissions/117f9fc0-a6f7-41b9-b583-6adfea7e1122

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_residual_from_eventual_product
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_harmonic_from_residual
import Theorems.Thm_AvramDividend_Classical_bv_scale_generator_harmonic_on_all_positive_reserves_ws01b
import Theorems.Thm_AvramDividend_Classical_scaledW_generator_harmonic_of_scale_harmonic_at_positive
import Theorems.Thm_AvramDividend_Classical_vcstar_scaledW_matched_weighted_jet_at_cstar
import Theorems.Thm_AvramDividend_Classical_generator_eq_at_barrier_of_weighted_jet

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Source generator equality at a positive optimal cap in Gaussian or BV cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (halt : 0 < X.σ ∨ X.BoundedVariation) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by
  have ha : 0 < (cstar W).toReal := ENNReal.toReal_pos hcpos.ne' hc.ne
  have hsource :
      X.GeneratorIntegrable
        (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal))
        (cstar W).toReal ∧
      X.generator
        (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal))
        (cstar W).toReal -
        q * divE (W (cstar W).toReal) (scaleDeriv W (cstar W).toReal) = 0 := by
    rcases halt with hσ | hbv
    · obtain ⟨φ, hφ, hroot⟩ :=
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
      exact scaledW_generator_harmonic_of_scale_harmonic_at_positive
        X q W (cstar W).toReal ha
        (hscale _ ha).1 (hscale _ ha).2
    · have hscale :=
        bv_scale_generator_harmonic_on_all_positive_reserves_ws01b
          X hX hbv q hq W hW
      exact scaledW_generator_harmonic_of_scale_harmonic_at_positive
        X q W (cstar W).toReal ha
        (hscale _ ha).1 (hscale _ ha).2
  have hs :
      0 < X.σ ∨ X.BoundedVariation ∨
        ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
    rcases halt with hσ | hbv
    · exact Or.inl hσ
    · exact Or.inr (Or.inl hbv)
  obtain ⟨hval, hder, hweighted⟩ :=
    vcstar_scaledW_matched_weighted_jet_at_cstar
      X hX q hq W hW hc hcpos hs
  obtain ⟨hdom, heq⟩ :=
    generator_eq_at_barrier_of_weighted_jet
      X (vcstar W)
      (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal))
      (cstar W).toReal hval hder hweighted
  refine ⟨hdom.mpr hsource.1, ?_⟩
  rw [heq, hval (cstar W).toReal le_rfl]
  exact hsource.2

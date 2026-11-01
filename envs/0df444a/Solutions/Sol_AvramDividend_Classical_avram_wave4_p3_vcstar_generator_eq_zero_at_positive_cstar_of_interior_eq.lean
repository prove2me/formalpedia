-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_interior_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:05:19.553188+00:00
-- url     : https://prove2.me/submissions/b7b6fcf5-3173-4d06-9c28-33bec90e1307

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_of_pure_C2_interior

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Original smoothness alternatives, with strict-interior harmonicity explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator (vcstar W) x - q * vcstar W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by
  by_cases hreg : 0 < X.σ ∨ X.BoundedVariation
  · exact vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
      X hX q hq W hW hc hcpos hreg
  · have hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
      rcases h_smooth with hσ | hbv | hC2case
      · exact (hreg (Or.inl hσ)).elim
      · exact (hreg (Or.inr hbv)).elim
      · exact hC2case
    have hσ0 : X.σ = 0 :=
      le_antisymm (le_of_not_gt (fun hσ => hreg (Or.inl hσ))) X.σ_nonneg
    have hnbv : ¬ X.BoundedVariation := fun hbv => hreg (Or.inr hbv)
    exact
      avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_of_pure_C2_interior
        X hX q hq W hW hc hcpos hσ0 hnbv hC2 hinside

-- Prove2me | solution 3 for AvramDividend.Classical.vcstar_hjb_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:05:10.083018+00:00
-- url     : https://prove2.me/submissions/000ffddb-bb61-4cd8-b3fe-8356111d56be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_vcstar_generator_integrable_at_positive_cap_of_global_C2
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_residual_continuousAt_positive_cap_of_pure_C2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped Topology NNReal ENNReal

/-- Positive-cap HJB from right-continuity of the original generator residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      max (X.generator (vcstar W) (cstar W).toReal -
           q * vcstar W (cstar W).toReal)
          (1 - deriv (vcstar W) (cstar W).toReal) = 0 := by
  have ha : 0 < (cstar W).toReal := ENNReal.toReal_pos hcpos.ne' hc.ne
  have hder :=
    vcstar_deriv_eq_one_at_positive_cstar
      X hX q hq W hW hc hcpos h_smooth
  by_cases hreg : 0 < X.σ ∨ X.BoundedVariation
  · obtain ⟨hdom, hres⟩ :=
      vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
        X hX q hq W hW hc hcpos hreg
    refine ⟨hdom, ?_⟩
    rw [hder, hres]
    simp
  · have hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
      rcases h_smooth with hσ | hbv | hC2case
      · exact (hreg (Or.inl hσ)).elim
      · exact (hreg (Or.inr hbv)).elim
      · exact hC2case
    have hσ0 : X.σ = 0 :=
      le_antisymm (le_of_not_gt (fun hσ => hreg (Or.inl hσ))) X.σ_nonneg
    have hnbv : ¬ X.BoundedVariation := fun hbv => hreg (Or.inr hbv)
    have hcont :=
      avram_wave4_p3_vcstar_generator_residual_continuousAt_positive_cap_of_pure_C2
        X hX q hq W hW hc hcpos hσ0 hnbv hC2
    have hevent : ∀ᶠ y in 𝓝[>] (cstar W).toReal,
        X.generator (vcstar W) y - q * vcstar W y ≤ 0 := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hgen y hy).2
    have hle :
        X.generator (vcstar W) (cstar W).toReal -
          q * vcstar W (cstar W).toReal ≤ 0 :=
      le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hevent
    have hdom :=
      avram_wave4_05a_vcstar_generator_integrable_at_positive_cap_of_global_C2
        X q W hW ha hC2
    refine ⟨hdom, ?_⟩
    rw [hder]
    simpa using max_eq_right hle

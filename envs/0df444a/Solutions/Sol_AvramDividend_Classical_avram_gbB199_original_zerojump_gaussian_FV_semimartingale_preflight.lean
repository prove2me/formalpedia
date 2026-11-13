-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:38:31.482762+00:00
-- url     : https://prove2.me/submissions/c56d8fd2-a7b9-4ea4-9936-4cd9cdbfbc46

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_avram_gbB173_original_postpayment_dividend_locally_bounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine source Gaussian martingale and original postpayment FV preflight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Martingale (fun t ω => X.X t ω - (t : ℝ) * X.c)
      𝓕.rightCont P ∧
    Martingale (fun t ω =>
      (X.X t ω - (t : ℝ) * X.c) ^ 2 -
        (t : ℝ) * X.σ ^ 2) 𝓕.rightCont P ∧
    (∀ ω, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => rightLimit D t ω) Set.univ) ∧
    (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X.X t ω)) ∧
    ∀ t ω, x + X.X t ω - rightLimit D t ω =
      (X.X t ω - (t : ℝ) * X.c) +
        (x + (t : ℝ) * X.c - rightLimit D t ω) := by
  refine ⟨avram_wave6_03_original_rightCont_zerojump_centered_source_martingale X hν, ?_, ?_, ?_, ?_⟩
  · exact avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale X hν
  · intro ω
    exact avram_gbB173_original_postpayment_dividend_locally_bounded_variation D hD ω
  · exact avram_ubv_top11_original_zero_nu_global_continuous_ae X hν
  · intro t ω
    ring

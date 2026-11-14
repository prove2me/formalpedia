-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB266_original_zerojump_good_cell_fixed_level_gaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:56:53.029175+00:00
-- url     : https://prove2.me/submissions/381cbd68-6b9b-4d48-9cea-e46a7e15a93b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_gbB261_original_good_dividend_cell_fixed_level_gaussian_hit_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB265_original_zerojump_unscaled_increment_gaussian_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original zero-jump unbounded-variation reserve has finite-cell Gaussian anti-concentration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t u : ℝ≥0) (hst : s < t) (htu : t < u)
    (x b epsilon : ℝ) (hEps : 0 ≤ epsilon) :
    P {ω | D u ω - D s ω ≤ epsilon ∧
      x + X.X t ω - rightLimit D t ω = b} ≤
      ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi *
          (((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * ((t - s : ℝ≥0) : NNReal) : ℝ))))⁻¹) *
        ENNReal.ofReal epsilon := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hσ : 0 < X.σ :=
    avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos X hBV hν
  have hv : 0 < (NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * ((t - s : ℝ≥0) : NNReal) := by
    apply mul_pos
    · change (0 : ℝ) < X.σ ^ 2
      positivity
    · exact tsub_pos_of_lt hst
  have hLaw :=
    avram_gbB265_original_zerojump_unscaled_increment_gaussian_law X hν hσ s t hst.le
  exact avram_gbB261_original_good_dividend_cell_fixed_level_gaussian_hit_bound
    X D hD s t u hst.le htu x b epsilon hEps
    (((t - s : ℝ≥0) : ℝ) * X.c)
    ((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * ((t - s : ℝ≥0) : NNReal))
    hv hLaw

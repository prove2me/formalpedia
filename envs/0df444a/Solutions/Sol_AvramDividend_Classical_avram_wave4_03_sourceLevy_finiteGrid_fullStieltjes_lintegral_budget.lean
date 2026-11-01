-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_lintegral_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:59:14.431674+00:00
-- url     : https://prove2.me/submissions/8db51a3a-2643-4014-a6e9-fd0ab7e6a005

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
/-- The exact original-source stochastic budget holds in ENNReal
for the full Stieltjes finite-grid dividend cash, enabling Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ∂P) ≤
    ENNReal.ofReal (∫ ω,
      Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by
  have hI := avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_cash_integrable
    X D hD θ hθ u hu n
  have hCash := avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
    X D hD θ hθ u hu n
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hCash.1)]
  exact ENNReal.ofReal_le_ofReal hCash.2

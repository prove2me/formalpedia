-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_lintegral_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:16:09.211818+00:00
-- url     : https://prove2.me/submissions/d7820a67-58a8-40fb-9c37-5cc5df0bf000

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_initial_rightAtom_discountedCash_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_mass_expected_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-Lévy true initial atom and all full Stieltjes grid cash in ENNReal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hu0 : u 0 = 0) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω) ∂P) +
    (∫⁻ ω, ENNReal.ofReal (θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ∂P) ≤ 1 := by
  have hf := avram_wave4_03_sourceLevy_initial_rightAtom_discountedCash_L1
    X D hD θ hθ
  have hg := avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_cash_integrable
    X D hD θ hθ u hu n
  have hGpos := (avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
    X D hD θ hθ u hu n).1
  have hbudget := avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_mass_expected_budget
    X D hD θ hθ u hu hu0 n
  rw [← ofReal_integral_eq_lintegral_ofReal hf.1
    (Filter.Eventually.of_forall (fun ω => (hf.2 ω).1))]
  rw [← ofReal_integral_eq_lintegral_ofReal hg
    (Filter.Eventually.of_forall hGpos)]
  have hfn : 0 ≤ (∫ ω, θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω ∂P) :=
    integral_nonneg (fun ω => (hf.2 ω).1)
  have hgn : 0 ≤ (∫ ω, θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ∂P) :=
    integral_nonneg hGpos
  rw [← ENNReal.ofReal_add hfn hgn]
  simpa using ENNReal.ofReal_le_ofReal hbudget

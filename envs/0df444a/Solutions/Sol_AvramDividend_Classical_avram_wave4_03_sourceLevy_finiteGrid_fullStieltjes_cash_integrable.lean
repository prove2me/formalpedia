-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_cash_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:54:57.996386+00:00
-- url     : https://prove2.me/submissions/cea70bc6-f180-4871-b803-299ff030777e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_exponential_postPayment_controlLoss_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_cash_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_cash_le_exponential_controlLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
/-- Integrability of full Stieltjes cash from original source Lévy products. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    Integrable (fun ω => θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) P := by
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)
  let B : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(θ * rightLimit D t ω))
  have hCashSM :
      AEStronglyMeasurable (fun ω => θ * ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * B (u (i + 1)) ω *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) P := by
    exact avram_wave4_03_sourceLevy_finiteGrid_cash_aestronglyMeasurable
      X D hD θ hθ u n
  have hUpperTerm (i : ℕ) :
      Integrable (fun ω =>
        Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)) P := by
    exact avram_wave4_03_sourceLevy_exponential_postPayment_controlLoss_L1
      X D hD θ hθ (u i) (u (i + 1))
  have hUpperInt : Integrable (fun ω =>
      ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)) P := by
    apply integrable_finset_sum
    intro i hi
    exact hUpperTerm i
  have hCashPos (ω : Ω) :
      0 ≤ θ * ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * B (u (i + 1)) ω *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) := by
    exact (avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
      X D hD θ hθ u hu n).1 ω
  have hPoint (ω : Ω) :
      θ * ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * B (u (i + 1)) ω *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ≤
      ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω) := by
    exact avram_wave4_03_sourceLevy_finiteGrid_cash_le_exponential_controlLoss
      X D hD θ hθ u hu n ω
  have hNorm : ∀ᵐ ω ∂P,
      ‖θ * ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * B (u (i + 1)) ω *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)‖ ≤
      ‖∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)‖ := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hCashPos ω),
      abs_of_nonneg (le_trans (hCashPos ω) (hPoint ω))]
    exact hPoint ω
  change Integrable (fun ω => θ * ∑ i ∈ Finset.range n,
    Z (u (i + 1)) ω * B (u (i + 1)) ω *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) P
  exact Integrable.mono hUpperInt hCashSM hNorm

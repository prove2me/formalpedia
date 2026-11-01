-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_doubleLintegral_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:02:55.647015+00:00
-- url     : https://prove2.me/submissions/70aa7915-fa25-4171-b17e-4935b6ebb7a3

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_fullStieltjes_cellIntegral_eq_finiteGrid_cashENNReal
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_lintegral_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Genuine expected double Stieltjes cash budget with the original Lévy
martingale and every type of dividend-measure mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫⁻ ω, ∫⁻ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        ENNReal.ofReal (θ *
          Real.exp (θ * X.X (u (i + 1)) ω -
            (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    ENNReal.ofReal (∫ ω,
      Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by
  calc
    _ = (∫⁻ ω, ENNReal.ofReal (θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ∂P) := by
        apply lintegral_congr_ae
        filter_upwards [] with ω
        exact avram_wave4_03_sourceLevy_fullStieltjes_cellIntegral_eq_finiteGrid_cashENNReal
          X D hD θ hθ u hu n ω
    _ ≤ _ := avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_lintegral_budget
      X D hD θ hθ u hu n

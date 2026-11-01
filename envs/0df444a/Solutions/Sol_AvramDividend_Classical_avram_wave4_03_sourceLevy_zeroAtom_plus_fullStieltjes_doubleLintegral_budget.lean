-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_fullStieltjes_doubleLintegral_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:26:03.158044+00:00
-- url     : https://prove2.me/submissions/c021c9eb-e2f1-486b-ad8c-d22da4f8242e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_fullStieltjes_cellIntegral_eq_finiteGrid_cashENNReal
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_lintegral_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual time-zero atom plus every random Ioc Stieltjes cell in expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hu0 : u 0 = 0) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω) ∂P) +
    (∫⁻ ω, ∫⁻ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        ENNReal.ofReal (θ * Real.exp
          (θ * X.X (u (i + 1)) ω -
            (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by
  calc
    _ = (∫⁻ ω, ENNReal.ofReal (θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω) ∂P) +
      (∫⁻ ω, ENNReal.ofReal (θ * ∑ i ∈ Finset.range n,
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ∂P) := by
          congr 1
          apply lintegral_congr_ae
          filter_upwards [] with ω
          exact avram_wave4_03_sourceLevy_fullStieltjes_cellIntegral_eq_finiteGrid_cashENNReal
            X D hD θ hθ u hu n ω
    _ ≤ 1 := avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_lintegral_budget
      X D hD θ hθ u hu hu0 n

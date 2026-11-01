-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_realStieltjes_step_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:00:36.805991+00:00
-- url     : https://prove2.me/submissions/6b04c165-3959-4ea4-8e44-2ebea73c7433

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_realStieltjes_cellStep_integral_eq_gridMass
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_mass_expected_budget
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Actual original Lévy finite-step full Stieltjes expected budget, including
the genuine time-zero right-dividend atom and all positive-time payment mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hu0 : u 0 = 0) (n : ℕ) :
    (∫ ω, θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω ∂P) +
    (∫ ω, ∫ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        θ * Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by
  have hsum (ω : Ω) :
      (∑ i ∈ Finset.range n,
        (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal *
        (θ * Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))) =
      θ * ∑ i ∈ Finset.range n,
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [dividendMeasure_Ioc_rightLimit D hD ω (u i) (u (i + 1))]
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr
      (avram_wave3_03_dividendStrategy_rightLimit_monotone
        D hD ω (hu (Nat.le_succ i))))]
    ring
  have hpath : (∫ ω, ∫ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        θ * Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω))
      else 0 ∂dividendMeasure D ω ∂P) =
      (∫ ω, θ * ∑ i ∈ Finset.range n,
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ∂P) := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [avram_wave4_03_sourceLevy_realStieltjes_cellStep_integral_eq_gridMass
      X D θ u n ω hD]
    exact hsum ω
  rw [hpath]
  exact avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_mass_expected_budget
    X D hD θ hθ u hu hu0 n
-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_mass_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:50:21.608526+00:00
-- url     : https://prove2.me/submissions/0d78c813-3ae9-4484-9ee7-5fc647fda573

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hu0 : u 0 = 0) (n : ℕ) :
    (∫ ω, θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω ∂P) +
    (∫ ω, θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ∂P) ≤ 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let B0 : Ω → ℝ := fun ω => Real.exp (-(θ * rightLimit D 0 ω))
  have hD0 (ω : Ω) : 0 ≤ rightLimit D 0 ω := by
    simpa only [hD.1 ω] using dividendStrategy_le_rightLimit D hD ω (0 : ℝ≥0)
  have hB0bound (ω : Ω) : 0 ≤ B0 ω ∧ B0 ω ≤ 1 := by
    constructor
    · exact (Real.exp_pos _).le
    · change Real.exp (-(θ * rightLimit D 0 ω)) ≤ 1
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hθ (hD0 ω)))
  have hB0meas : Measurable B0 := by
    have hm : Measurable (rightLimit D (0 : ℝ≥0)) :=
      (dividendStrategy_rightLimit_adapted_rightCont D hD 0).mono
        (𝓕.rightCont.le 0) le_rfl
    exact ((measurable_const.mul hm).neg).exp
  have hB0int : Integrable B0 P :=
    Integrable.of_bound hB0meas.aestronglyMeasurable 1 (by
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hB0bound ω).1]
      exact (hB0bound ω).2)
  have hfirst (ω : Ω) :
      θ * B0 ω * rightLimit D 0 ω ≤ 1 - B0 ω := by
    have hh := avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
      θ 0 (rightLimit D 0 ω) hθ (hD0 ω)
    simpa [B0] using hh
  have hfirstpos (ω : Ω) :
      0 ≤ θ * B0 ω * rightLimit D 0 ω :=
    mul_nonneg (mul_nonneg hθ (hB0bound ω).1) (hD0 ω)
  have hfirstint : Integrable (fun ω : Ω => (1 : ℝ) - B0 ω) P :=
    (integrable_const (μ := P) (c := (1 : ℝ))).sub hB0int
  have hfirstbudget :
      (∫ ω, θ * B0 ω * rightLimit D 0 ω ∂P) ≤
      (∫ ω, (1 : ℝ) - B0 ω ∂P) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall hfirstpos)
      hfirstint (Filter.Eventually.of_forall hfirst)
  have hgridbudget := (avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
    X D hD θ hθ u hu n).2
  have hright : (∫ ω,
      Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) =
      (∫ ω, B0 ω ∂P) := by
    apply integral_congr_ae
    filter_upwards [] with ω; simp [B0, hu0, X.X_zero]
  rw [hright] at hgridbudget
  change (∫ ω, θ * B0 ω * rightLimit D 0 ω ∂P) +
    (∫ ω, θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ∂P) ≤ 1
  calc
    _ ≤ (∫ ω, (1 : ℝ) - B0 ω ∂P) +
      (∫ ω, B0 ω ∂P) := add_le_add hfirstbudget hgridbudget
    _ = 1 := by rw [integral_sub (integrable_const (μ := P) (c := (1 : ℝ))) hB0int]; simp

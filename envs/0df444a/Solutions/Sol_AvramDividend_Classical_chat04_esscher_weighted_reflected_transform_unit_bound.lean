-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_reflected_transform_unit_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:08:38.502088+00:00
-- url     : https://prove2.me/submissions/06d3122f-f85e-4392-a86f-9fa348fe2667

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_reflected_infimum_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (β θ : ℝ) (hβ : 0 < β) (hθ : 0 ≤ θ) :
    0 ≤ (∫ ω : Ω,
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) ∧
    (∫ ω : Ω,
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) ≤ 1 / β := by
  let g : Ω → ℝ := fun ω =>
    Real.exp (-β * max 0
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β
  let m : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X t ω -
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)
  have hI : Integrable (fun ω => g ω * m ω) P := by
    simpa only [g, m] using
      chat04_esscher_weighted_reflected_infimum_integrable
        X t β θ hβ hθ
  have hM : Integrable m P := by
    simpa only [m] using esscher_exp_process_integrable X θ hθ t
  have hUnit : (∫ ω, m ω ∂P) = 1 := by
    simpa only [m, SpectrallyNegativeLevy.ψ] using
      levy_compensated_exponential_expectation_one X t θ hθ
  have hgNonneg : ∀ ω : Ω, 0 ≤ g ω := by
    intro ω
    exact div_nonneg (Real.exp_nonneg _) hβ.le
  have hgUpper : ∀ ω : Ω, g ω ≤ 1 / β := by
    intro ω
    have hbound : 0 ≤ max 0
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) :=
      le_max_left _ _
    have hpow : -β * max 0
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) hbound
    exact div_le_div_of_nonneg_right
      (Real.exp_le_one_iff.mpr hpow) hβ.le
  change 0 ≤ (∫ ω, g ω * m ω ∂P) ∧
    (∫ ω, g ω * m ω ∂P) ≤ 1 / β
  constructor
  · apply integral_nonneg
    intro ω
    exact mul_nonneg (hgNonneg ω) (Real.exp_nonneg _)
  · have hUpper : (∫ ω, g ω * m ω ∂P) ≤
        (∫ ω, (1 / β) * m ω ∂P) := by
      apply integral_mono_ae hI (hM.const_mul (1 / β))
      filter_upwards [] with ω
      exact mul_le_mul_of_nonneg_right (hgUpper ω) (Real.exp_nonneg _)
    calc
      (∫ ω, g ω * m ω ∂P) ≤
          (∫ ω, (1 / β) * m ω ∂P) := hUpper
      _ = 1 / β := by
        rw [integral_const_mul, hUnit, mul_one]

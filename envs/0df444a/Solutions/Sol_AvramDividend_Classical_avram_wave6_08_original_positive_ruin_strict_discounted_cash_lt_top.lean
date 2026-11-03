-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_ruin_strict_discounted_cash_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:01:41.700834+00:00
-- url     : https://prove2.me/submissions/96e6dee4-e153-4a31-b557-dd3a02c6606c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original pathwise complete discounted cash strictly before finite positive
ruin is finite, without counting the ruin right-payment atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ) :
    (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
  let μ : Measure ℝ := dividendMeasure D ω
  have hmass :
      μ (Ioo (0 : ℝ) (τ : ℝ)) =
        ENNReal.ofReal (D τ ω - rightLimit D (0 : ℝ≥0) ω) :=
    avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
      D hD ω 0 τ hτ
  have hbound :
      (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
          μ (Ioo (0 : ℝ) (τ : ℝ)) := by
    have hae : ∀ᵐ t ∂μ.restrict (Ioo (0 : ℝ) (τ : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ≤ (1 : ℝ≥0∞) := by
      refine (ae_restrict_mem measurableSet_Ioo).mono ?_
      intro t ht
      have hqt : 0 ≤ q * t := mul_nonneg hq (le_of_lt ht.1)
      have hexp : Real.exp (-(q * t)) ≤ 1 := by
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqt)
      simpa using (ENNReal.ofReal_le_ofReal hexp)
    calc
      (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
        ∫⁻ t in Ioo (0 : ℝ) (τ : ℝ), (1 : ℝ≥0∞) ∂μ :=
          lintegral_mono_ae hae
      _ = μ (Ioo (0 : ℝ) (τ : ℝ)) := by simp
  change (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) < ⊤
  rw [hmass] at hbound
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

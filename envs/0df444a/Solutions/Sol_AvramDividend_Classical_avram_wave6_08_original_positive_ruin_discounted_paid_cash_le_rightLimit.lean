-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_ruin_discounted_paid_cash_le_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:56:28.655518+00:00
-- url     : https://prove2.me/submissions/881c7d8b-ad8d-429b-86d6-3db4fd7046e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Actual stopped paid cash before a positive finite ruin time is bounded
by the original cumulative right-limit dividend amount at ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ) :
    (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D τ ω) := by
  let μ : Measure ℝ := dividendMeasure D ω
  have hclip :
      paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ) =
        Ico (0 : ℝ) (τ : ℝ) := by
    simpa using
      (avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
        τ hτ (τ : ℝ) (NNReal.coe_nonneg τ))
  have hweight :
      (∫⁻ t in Ico (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
          μ (Ico (0 : ℝ) (τ : ℝ)) := by
    have hae : ∀ᵐ t ∂μ.restrict (Ico (0 : ℝ) (τ : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ≤ (1 : ℝ≥0∞) := by
      refine (ae_restrict_mem measurableSet_Ico).mono ?_
      intro t ht
      have hqt : 0 ≤ q * t := mul_nonneg hq ht.1
      have hexp : Real.exp (-(q * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqt)
      simpa using (ENNReal.ofReal_le_ofReal hexp)
    calc
      (∫⁻ t in Ico (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
        ∫⁻ t in Ico (0 : ℝ) (τ : ℝ), (1 : ℝ≥0∞) ∂μ :=
          lintegral_mono_ae hae
      _ = μ (Ico (0 : ℝ) (τ : ℝ)) := by simp
  have hsubset : Ico (0 : ℝ) (τ : ℝ) ⊆
      Icc (0 : ℝ) (τ : ℝ) := by
    intro t ht
    exact ⟨ht.1, le_of_lt ht.2⟩
  calc
    (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
      (∫⁻ t in Ico (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) := by rw [hclip]
    _ ≤ μ (Ico (0 : ℝ) (τ : ℝ)) := hweight
    _ ≤ μ (Icc (0 : ℝ) (τ : ℝ)) := measure_mono hsubset
    _ = ENNReal.ofReal (rightLimit D τ ω) :=
      avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω τ

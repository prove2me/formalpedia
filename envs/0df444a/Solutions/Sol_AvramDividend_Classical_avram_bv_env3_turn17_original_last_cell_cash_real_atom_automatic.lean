-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn17_original_last_cell_cash_real_atom_automatic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:42:51.923225+00:00
-- url     : https://prove2.me/submissions/0c416b72-214a-4ef8-9099-796e754f9fc4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn16_original_last_cell_closed_cash_toReal_splits_endpoint_atom
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original finite closed-horizon Stieltjes budget makes both cash pieces finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (a : ℝ) (ha : a < (T : ℝ)) :
    (∫⁻ t in paymentTimes σ ∩ Ioc a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hWhole :
      (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) < ⊤ := by
    simpa using
      (avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
        D hD ω σ T q hq)
  have hStrict :
      (∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≠ ⊤ := by
    have hle :
        (∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) ≤
        (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) := by
      apply lintegral_mono_set
      intro t ht
      exact ⟨ht.1, le_of_lt ht.2.2⟩
    exact ne_of_lt (lt_of_le_of_lt hle hWhole)
  have hAtom :
      (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≠ ⊤ := by
    have hle :
        (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) ≤
        (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) := by
      apply lintegral_mono_set
      intro t ht
      rcases ht with ⟨hpay, ht⟩
      rcases ht with rfl
      exact ⟨hpay, Set.mem_Iic.mpr le_rfl⟩
    exact ne_of_lt (lt_of_le_of_lt hle hWhole)
  exact avram_bv_env3_turn16_original_last_cell_closed_cash_toReal_splits_endpoint_atom
    D hD ω σ T q a ha hStrict hAtom

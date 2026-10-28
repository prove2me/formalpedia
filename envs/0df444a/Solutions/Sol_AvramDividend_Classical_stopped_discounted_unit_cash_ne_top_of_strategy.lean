-- Prove2me | solution 1 for AvramDividend.Classical.stopped_discounted_unit_cash_ne_top_of_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:02:02.781614+00:00
-- url     : https://prove2.me/submissions/a5e415c0-2139-41dc-9187-50da8591638a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every exact stopped discounted unit-interval cash integral is
    finite for an admissible dividend strategy at a finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ω : Ω) (k : ℕ) :
    (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      Ico (k : ℝ) ((k : ℝ) + 1),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤ := by
  let A : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  let B : Set ℝ := A ∩ Ico (k : ℝ) ((k : ℝ) + 1)
  have hA : MeasurableSet A :=
    (paymentTimes_measurable σ).inter measurableSet_Iic
  have hB : MeasurableSet B := hA.inter measurableSet_Ico
  have hBnonneg : ∀ t ∈ B, 0 ≤ t := by
    intro t ht
    exact ht.1.1.1
  have hDiscount :=
    discounted_stieltjes_lintegral_le_measure q hq
      (dividendMeasure D ω) B hB hBnonneg
  have hMass : (dividendMeasure D ω) B ≤
      (dividendMeasure D ω) A :=
    measure_mono (Set.inter_subset_left)
  have hFinite : (dividendMeasure D ω) A < ⊤ :=
    lt_top_iff_ne_top.mpr
      (dividendMeasure_paymentWindow_finite_of_strategy D hD ω σ T)
  exact (lt_of_le_of_lt (hDiscount.trans hMass) hFinite).ne

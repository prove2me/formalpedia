-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividend_window_real_integral_le_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:14:57.710862+00:00
-- url     : https://prove2.me/submissions/c5cd92e9-5b37-49fc-a044-9de266a85c5d

import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_le_cumulative
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_real_lintegral_bridge
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Real Stieltjes payouts inherit the pathwise cumulative-dividend budget
    through the verified real/ENNReal integral identification. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) :
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
       Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ D (T + 1) ω := by
  have hDnonneg : 0 ≤ D (T + 1) ω := by
    have h0 : D 0 ω = 0 := hD.1 ω
    have hmono : Monotone (fun t : ℝ≥0 => D t ω) := hD.2.1 ω
    calc
      0 = D 0 ω := h0.symm
      _ ≤ D (T + 1) ω := hmono (by simp)
  have hbound :=
    discounted_dividend_window_le_cumulative D hD q hq σ T ω
  have hbridge :=
    discounted_dividend_window_real_lintegral_bridge D hD q hq σ T ω
  rw [hbridge] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hDnonneg).mp hbound

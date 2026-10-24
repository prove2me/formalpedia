-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_le_right_scale_quotient_of_record_budgets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:07:03.083526+00:00
-- url     : https://prove2.me/submissions/1f130a8d-00a1-416b-8f4a-9afdb2a295e7

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_correct_geometric_renewal_quotient_of_record_bounds
import Theorems.Thm_AvramDividend_Classical_stopped_renewal_geometric_scale_ratio_upper
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! The immediate first-record estimate yields the right scale quotient under stochastic cell budgets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (W : ℝ → ℝ) (a q ε : ℝ)
    (hε : 0 ≤ ε) (hWright : 0 < W (a + ε))
    (hWa : 0 ≤ W a) (hWinc : W a < W (a + ε))
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤ (∑' n, w n ω))
    (hstep : ∀ n, (∫⁻ ω, w n ω ∂P) ≤
      ENNReal.ofReal (ε * (W a / W (a + ε)) ^ n)) :
    barrierSupValue X a q ≤
      ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by
  have hA : W (a + ε) ≠ 0 := ne_of_gt hWright
  have hdiff : W (a + ε) - W a ≠ 0 :=
    ne_of_gt (sub_pos.mpr hWinc)
  have hp : 0 ≤ W a / W (a + ε) :=
    div_nonneg hWa (le_of_lt hWright)
  have hplt : W a / W (a + ε) < 1 :=
    (div_lt_one hWright).mpr hWinc
  have hb := barrierSupValue_le_correct_geometric_renewal_quotient_of_record_bounds
    X a q ε (W a / W (a + ε)) hε hp hplt w hw hbudget hstep
  have halg := stopped_renewal_geometric_scale_ratio_upper W a ε hA hdiff
  rwa [halg] at hb

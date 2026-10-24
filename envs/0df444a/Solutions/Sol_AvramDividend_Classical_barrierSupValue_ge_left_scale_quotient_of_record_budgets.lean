-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_ge_left_scale_quotient_of_record_budgets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:07:12.485652+00:00
-- url     : https://prove2.me/submissions/57b598cd-a592-43c4-ba7b-36c729a8025f

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_correct_geometric_renewal_quotient_of_record_bounds
import Theorems.Thm_AvramDividend_Classical_stopped_renewal_geometric_scale_ratio_lower
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! The delayed first-record estimate yields the left scale quotient under stochastic cell budgets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (W : ℝ → ℝ) (a q ε : ℝ)
    (hε : 0 ≤ ε) (hWa : 0 < W a)
    (hWleft : 0 ≤ W (a - ε)) (hWinc : W (a - ε) < W a)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P, (∑' n, w n ω) ≤
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)))
    (hstep : ∀ n,
      ENNReal.ofReal (ε * (W (a - ε) / W a) ^ (n + 1)) ≤
      (∫⁻ ω, w n ω ∂P)) :
    ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
      barrierSupValue X a q := by
  have hA : W a ≠ 0 := ne_of_gt hWa
  have hdiff : W a - W (a - ε) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hWinc)
  have hp : 0 ≤ W (a - ε) / W a :=
    div_nonneg hWleft (le_of_lt hWa)
  have hplt : W (a - ε) / W a < 1 :=
    (div_lt_one hWa).mpr hWinc
  have hb := barrierSupValue_ge_correct_geometric_renewal_quotient_of_record_bounds
    X a q ε (W (a - ε) / W a) hε hp hplt w hw hbudget hstep
  have halg := stopped_renewal_geometric_scale_ratio_lower W a ε hA hdiff
  rwa [halg] at hb

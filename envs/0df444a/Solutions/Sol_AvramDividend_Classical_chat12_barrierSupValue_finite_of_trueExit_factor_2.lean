-- Prove2me | solution 2 for AvramDividend.Classical.chat12_barrierSupValue_finite_of_trueExit_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:27:25.023+00:00
-- url     : https://prove2.me/submissions/1fb0323a-0d74-4444-a5c2-8148e72a3e4a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_barrierSup_stopped_indicator_reward_le_killed_record_tsum
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_finite_of_trueExit_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p < 1)
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    barrierSupValue X a q < ∞ := by
  classical
  let w : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
    else 0
  have hw : ∀ n : ℕ, AEMeasurable (w n) P := by
    intro n
    exact (killed_firstRecord_discount_reward_measurable
      X a ((n : ℝ) * ε) ε q).aemeasurable
  have hbudget : ∀ᵐ ω ∂P,
      (∫⁻ t, if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑' n, w n ω) := by
    apply Filter.Eventually.of_forall
    intro ω
    simpa only [w] using
      (barrierSup_stopped_indicator_reward_le_killed_record_tsum
        X a q ε (le_of_lt hq) hε ω)
  have hUpper :=
    barrierSupValue_le_sum_expected_firstRecord_budgets
      X a q w hw hbudget
  have hFinite :=
    chat12_total_expected_upper_finite_of_trueExit_factor
      X hX q hq a ε ha hε p hp hp1 hExit
  exact lt_of_le_of_lt hUpper (by simpa only [w] using hFinite)

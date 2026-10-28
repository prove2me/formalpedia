-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_discountedReward_antitone_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:08:00.905674+00:00
-- url     : https://prove2.me/submissions/f1106500-c866-4e15-af81-96e357fe3e6d

import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Discounted stopped dividends decrease along reciprocal drawdown barriers. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (q : ℝ) :
    Antitone (fun n : ℕ =>
      ∫⁻ t in paymentTimes
        (barrierRuinTime X (1 / ((n : ℝ) + 1)) ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (runningSup X) ω)) := by
  intro i j hij
  have hbar : (1 : ℝ) / ((j : ℝ) + 1) ≤
      1 / ((i : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have hijreal : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact add_le_add_left hijreal 1
  have htime := barrierRuinTime_mono_barrier X
    (1 / ((j : ℝ) + 1)) (1 / ((i : ℝ) + 1)) hbar ω
  have hsub : paymentTimes
      (barrierRuinTime X (1 / ((j : ℝ) + 1)) ω) ⊆
      paymentTimes (barrierRuinTime X (1 / ((i : ℝ) + 1)) ω) := by
    intro t ht
    exact ⟨ht.1, ht.2.imp id (fun h => h.trans_le htime)⟩
  exact lintegral_mono_set hsub

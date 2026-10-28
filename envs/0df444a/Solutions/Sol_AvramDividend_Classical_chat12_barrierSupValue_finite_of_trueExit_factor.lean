-- Prove2me | solution 1 for AvramDividend.Classical.chat12_barrierSupValue_finite_of_trueExit_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:25:29.422954+00:00
-- url     : https://prove2.me/submissions/c2ab729e-176e-4942-a54a-bd6b274211f2

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_barrierSup_stopped_indicator_reward_le_killed_record_tsum
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_finite_of_trueExit_factor

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal


theorem s71_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q) (a ε : ℝ) (hε : 0 < ε) :
    barrierSupValue X a q ≤ (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) :=
  barrierSupValue_le_sum_expected_firstRecord_budgets X a q _
    (fun n => (killed_firstRecord_discount_reward_measurable X a ((n : ℝ) * ε) ε q).aemeasurable)
    (Filter.Eventually.of_forall fun ω =>
      barrierSup_stopped_indicator_reward_le_killed_record_tsum X a q ε hq.le hε ω)

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
    barrierSupValue X a q < ∞ :=
  lt_of_le_of_lt (s71_bound X q hq a ε hε)
    (chat12_total_expected_upper_finite_of_trueExit_factor X hX q hq a ε ha hε p hp hp1 hExit)

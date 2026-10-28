-- Prove2me | solution 2 for AvramDividend.Classical.chat12_barrierSupValue_ge_closed_form_of_trueExit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:29:28.457501+00:00
-- url     : https://prove2.me/submissions/2df1ab8c-0505-4d1c-9ec4-636d5133d614

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_stopped_firstRecord_grid_pathwise_budget
import Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_sum_expected_firstRecord_budgets
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_lower_geometric_closed_form

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (hq : 0 < q) (ha : 0 < a)
    (hε : 0 < ε) (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    ENNReal.ofReal ε * (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) ≤
      barrierSupValue X a q := by
  refine le_trans (chat12_total_expected_lower_geometric_closed_form X q a ε ha hε p hp hExit) ?_
  apply barrierSupValue_ge_sum_expected_firstRecord_budgets X a q
  · intro n
    simpa using chat08_record_grid_stopped_weights_aemeasurable X a 0 q ε (fun n => n + 1) n
  · exact Filter.Eventually.of_forall fun ω => by
      simpa using stopped_firstRecord_grid_pathwise_budget X ω a q 0 ε hq.le le_rfl hε

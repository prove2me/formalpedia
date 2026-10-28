-- Prove2me | solution 1 for AvramDividend.Classical.chat12_barrierSupValue_ge_closed_form_of_trueExit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:27:03.81566+00:00
-- url     : https://prove2.me/submissions/a04b5dfe-b341-4416-ab55-1c12c7a6a1e4

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_stopped_firstRecord_grid_pathwise_budget
import Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_sum_expected_firstRecord_budgets
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_lower_geometric_closed_form

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  classical
  let w : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
    else 0
  have hw : ∀ n : ℕ, AEMeasurable (w n) P := by
    simpa only [w, zero_add] using
      (chat08_record_grid_stopped_weights_aemeasurable
        X a 0 q ε (fun n => n + 1))
  have hbudget : ∀ᵐ ω ∂P,
      (∑' n, w n ω) ≤
        (∫⁻ t, if t ∈ paymentTimes (barrierRuinTime X a ω)
          then ENNReal.ofReal (Real.exp (-(q * t))) else 0
          ∂(dividendMeasure (runningSup X) ω)) := by
    apply Filter.Eventually.of_forall
    intro ω
    have h :=
      stopped_firstRecord_grid_pathwise_budget
        X ω a q 0 ε (le_of_lt hq) (le_refl (0 : ℝ)) hε
    simpa only [w, zero_add] using h
  have hLower :=
    barrierSupValue_ge_sum_expected_firstRecord_budgets
      X a q w hw hbudget
  have hTotal :=
    chat12_total_expected_lower_geometric_closed_form
      X q a ε ha hε p hp hExit
  exact le_trans (by simpa only [w] using hTotal) hLower

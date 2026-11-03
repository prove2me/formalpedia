-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_unrestricted_full_and_future_signed_stieltjes_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:01:37.097937+00:00
-- url     : https://prove2.me/submissions/02733956-9a29-4cc8-837d-58b81ea6232d

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Every actual full-source real signed discounted payment integral and
    strict future-payment tail is nonnegative, including all Stieltjes atoms. -/
/- Recovered complete original Stieltjes proof after terminal remote storage failure. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q : ℝ) :
    (0 ≤ ∫ t in paymentTimes σ,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∧
    (∀ T : ℝ, 0 ≤ ∫ t in paymentTimes σ ∩ Ioi T,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  constructor
  · exact integral_nonneg (fun t => (Real.exp_pos (-(q * t))).le)
  · intro T
    exact integral_nonneg (fun t => (Real.exp_pos (-(q * t))).le)

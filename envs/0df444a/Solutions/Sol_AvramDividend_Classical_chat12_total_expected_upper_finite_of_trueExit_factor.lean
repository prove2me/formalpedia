-- Prove2me | solution 1 for AvramDividend.Classical.chat12_total_expected_upper_finite_of_trueExit_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:04:11.945996+00:00
-- url     : https://prove2.me/submissions/5a3a13f9-eecc-48bb-aa2b-984020b87a0f

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_geometric_closed_form
import Theorems.Thm_AvramDividend_Classical_chat12_geometric_budget_lt_top_of_ratio_lt_one
import Mathlib.Analysis.Complex.Exponential

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
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) < ∞ := by
  have hUpper :=
    chat12_total_expected_upper_geometric_closed_form
      X hX q hq a ε ha hε p hp hExit
  have hFinite :=
    chat12_geometric_budget_lt_top_of_ratio_lt_one
      ε p (le_of_lt hε) hp hp1
  exact lt_of_le_of_lt hUpper hFinite

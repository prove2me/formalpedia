-- Prove2me | solution 1 for AvramDividend.Classical.chat12_total_expected_lower_scale_closed_form_of_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:02:15.713551+00:00
-- url     : https://prove2.me/submissions/07a4313d-a44e-43e1-8320-7cabe3068338

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_lower_geometric_closed_form
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
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a)
    (hExit : (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) :
    ENNReal.ofReal ε *
      (ENNReal.ofReal (W (a - ε) / W a) *
        (1 - ENNReal.ofReal (W (a - ε) / W a))⁻¹) ≤
      (∑' n : ℕ, (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) := by
  have hRatio : 0 ≤ W (a - ε) / W a :=
    div_nonneg hWleft (le_of_lt hWa)
  exact chat12_total_expected_lower_geometric_closed_form
    X q a ε ha hε (W (a - ε) / W a) hRatio hExit

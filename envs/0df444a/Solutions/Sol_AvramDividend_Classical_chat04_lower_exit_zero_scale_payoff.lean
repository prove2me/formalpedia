-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_exit_zero_scale_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:04:15.69876+00:00
-- url     : https://prove2.me/submissions/ae656b24-ca1f-47b1-b7dd-9592428af7a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_firstDowncrossing_value_le_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWzero : W 0 = 0) (a x : ℝ) (ω : Ω) :
    (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
     else 0) = 0 := by
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a - x) ω
  change (if D < U then
      ENNReal.ofReal (Real.exp (-(q * D.toReal))) *
        ENNReal.ofReal (W (x + X.X D.toNNReal ω))
      else 0) = 0
  by_cases h : D < U
  · have hfinite : D ≠ ⊤ := ne_of_lt (lt_of_lt_of_le h le_top)
    have hd : (D.toNNReal : ℝ≥0∞) =
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by
      simpa only [D, twoSidedExitDownTime] using
        (ENNReal.coe_toNNReal hfinite)
    have hhit : X.X D.toNNReal ω ≤ -x :=
      AvramDividend.Classical.chat04_firstDowncrossing_value_le_threshold
        X (-x) ω D.toNNReal hd
    have hnonpos : x + X.X D.toNNReal ω ≤ 0 := by linarith
    have hWnonpos : W (x + X.X D.toNNReal ω) = 0 := by
      rcases eq_or_lt_of_le hnonpos with heq | hlt
      · rw [heq]
        exact hWzero
      · exact hW.1 _ hlt
    simp only [if_pos h, hWnonpos, ENNReal.ofReal_zero, mul_zero]
  · simp only [if_neg h]

-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_exit_scale_creeping_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:26:22.736736+00:00
-- url     : https://prove2.me/submissions/316656ee-cd7b-41fd-844b-cc430bc91630

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
    (a x : ℝ) (ω : Ω) :
    (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
     else 0) =
    (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          (if x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0 then
             ENNReal.ofReal (W 0)
           else 0)
     else 0) := by
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a - x) ω
  change (if D < U then
      ENNReal.ofReal (Real.exp (-(q * D.toReal))) *
        ENNReal.ofReal (W (x + X.X D.toNNReal ω))
    else 0) =
    (if D < U then
      ENNReal.ofReal (Real.exp (-(q * D.toReal))) *
        (if x + X.X D.toNNReal ω = 0 then ENNReal.ofReal (W 0) else 0)
    else 0)
  by_cases h : D < U
  · have hfinite : D ≠ ⊤ := ne_of_lt (lt_of_lt_of_le h le_top)
    have hd : (D.toNNReal : ℝ≥0∞) =
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by
      simpa only [D, twoSidedExitDownTime] using
        (ENNReal.coe_toNNReal hfinite)
    have hdown : X.X D.toNNReal ω ≤ -x :=
      AvramDividend.Classical.chat04_firstDowncrossing_value_le_threshold
        X (-x) ω D.toNNReal hd
    have hnonpos : x + X.X D.toNNReal ω ≤ 0 := by linarith
    have hval : ENNReal.ofReal (W (x + X.X D.toNNReal ω)) =
        (if x + X.X D.toNNReal ω = 0 then ENNReal.ofReal (W 0) else 0) := by
      rcases eq_or_lt_of_le hnonpos with hzero | hneg
      · simpa [hzero]
      · have hn : x + X.X D.toNNReal ω ≠ 0 := ne_of_lt hneg
        simp only [if_neg hn, hW.1 _ hneg, ENNReal.ofReal_zero]
    simp only [if_pos h, hval]
  · simp only [if_neg h]

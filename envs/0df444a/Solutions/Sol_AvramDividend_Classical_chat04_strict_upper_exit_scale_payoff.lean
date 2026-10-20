-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:46:29.989101+00:00
-- url     : https://prove2.me/submissions/620e8728-a56d-4830-9c68-171452537ca4

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    (W : ℝ → ℝ) (q a x : ℝ) (hxa : x ≤ a) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
     else 0) =
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a)
     else 0) := by
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a - x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  change (if U < D then
      ENNReal.ofReal (Real.exp (-(q * U.toReal))) *
        ENNReal.ofReal (W (x + X.X U.toNNReal ω))
    else 0) =
    (if U < D then
      ENNReal.ofReal (Real.exp (-(q * U.toReal))) *
        ENNReal.ofReal (W a)
    else 0)
  by_cases h : U < D
  · have hfinite : U ≠ ⊤ := ne_of_lt (lt_of_lt_of_le h le_top)
    have hu : (U.toNNReal : ℝ≥0∞) =
        (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) := by
      simpa only [U, twoSidedExitUpTime] using
        (ENNReal.coe_toNNReal hfinite)
    have hhit : X.X U.toNNReal ω = a - x :=
      AvramDividend.Classical.firstUpcrossing_value_eq_threshold
        X (a - x) (sub_nonneg.mpr hxa) ω U.toNNReal hu
    have hb : W (x + X.X U.toNNReal ω) = W a := by
      rw [hhit]
      congr 1
      ring
    simp only [if_pos h, hb]
  · simp only [if_neg h]

-- Prove2me | solution 1 for AvramDividend.Classical.chat04_two_sided_strict_exit_no_finite_tie
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:04:39.088717+00:00
-- url     : https://prove2.me/submissions/3c3ff0c6-24b9-4bf3-9518-cbacb382f7a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
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
    (a x : ℝ) (ha : 0 < a) (hxa : x ≤ a) (ω : Ω) :
    twoSidedExitUpTime X (a - x) ω = twoSidedExitDownTime X (-x) ω →
      twoSidedExitUpTime X (a - x) ω = ⊤ := by
  intro hTie
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a - x) ω
  have hTie' : U = twoSidedExitDownTime X (-x) ω := hTie
  change U = ⊤
  by_contra hfinite
  have hu : (U.toNNReal : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) := by
    simpa only [U, twoSidedExitUpTime] using
      (ENNReal.coe_toNNReal hfinite)
  have hd : (U.toNNReal : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by
    calc
      (U.toNNReal : ℝ≥0∞) = U := ENNReal.coe_toNNReal hfinite
      _ = twoSidedExitDownTime X (-x) ω := hTie'
      _ = (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := rfl
  have hup : X.X U.toNNReal ω = a - x :=
    AvramDividend.Classical.firstUpcrossing_value_eq_threshold
      X (a - x) (sub_nonneg.mpr hxa) ω U.toNNReal hu
  have hdown : X.X U.toNNReal ω ≤ -x :=
    AvramDividend.Classical.chat04_firstDowncrossing_value_le_threshold
      X (-x) ω U.toNNReal hd
  linarith

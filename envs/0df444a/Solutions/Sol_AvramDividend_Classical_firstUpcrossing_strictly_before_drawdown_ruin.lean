-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_strictly_before_drawdown_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T12:59:46.582632+00:00
-- url     : https://prove2.me/submissions/0a45e7b6-0ffa-426b-93e7-119dff0e622b

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_pre_ruin_strict_of_right_continuous
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
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBefore : ∀ t : ℝ≥0, t < u → reflectedSup X t ω ≤ a) :
    (u : ℝ≥0∞) <
      (⨅ (t : ℝ≥0) (_ : a < reflectedSup X t ω), (t : ℝ≥0∞)) := by
  exact firstUpcrossing_pre_ruin_strict_of_right_continuous
    X a b ha hb ω u hu hBefore (reflectedSup_right_continuous X ω u)

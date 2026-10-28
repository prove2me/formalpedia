-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_upExit_before_controlledRuin_iff_rawExit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:01:41.411356+00:00
-- url     : https://prove2.me/submissions/d7f00c4a-47f8-4e84-85ce-538c0f0426d0

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_successful_upcrossing_iff_raw_lower_exit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The strict raw lower-exit condition can replace controlled ruin in the
    exact finite-or-infinite upcrossing event used for dividend valuation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) :
    (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
        ruinTime X x (barrierStrategy X x a) ω ↔
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by
  classical
  by_cases htop :
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) = ⊤
  · simp only [htop, not_top_lt]
  · let u : ℝ≥0 :=
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)).toNNReal
    have hu : (u : ℝ≥0∞) =
        (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) := by
      exact ENNReal.coe_toNNReal htop
    simpa only [hu] using
      (barrierStrategy_successful_upcrossing_iff_raw_lower_exit
        X x a ha hx0 hxa ω u hu)

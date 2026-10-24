-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_translated_Ioc_eq_of_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:04:11.487985+00:00
-- url     : https://prove2.me/submissions/78b578f5-4e0d-40b4-8ad8-48cacf41f0d8

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Matching translated increments give equal Stieltjes interval masses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D E : ℝ≥0 → Ω → ℝ) (ω : Ω) (u t : ℝ≥0)
    (hmD : Monotone (fun r : ℝ => D r.toNNReal ω))
    (hmE : Monotone (fun r : ℝ => E r.toNNReal ω))
    (hrD : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => D v.toNNReal ω) r = D r.toNNReal ω)
    (hrE : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => E v.toNNReal ω) r = E r.toNNReal ω)
    (hinc : D (u + t) ω - D u ω = E t ω - E 0 ω) :
    (dividendMeasure D ω)
        (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) =
      (dividendMeasure E ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := by
  rw [dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
        D ω (u : ℝ) ((u + t : ℝ≥0) : ℝ) hmD hrD,
      dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
        E ω (0 : ℝ) (t : ℝ) hmE hrE]
  simpa using congrArg ENNReal.ofReal hinc

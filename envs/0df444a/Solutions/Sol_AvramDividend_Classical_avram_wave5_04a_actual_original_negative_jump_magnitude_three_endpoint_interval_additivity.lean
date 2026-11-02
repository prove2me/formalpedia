-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_original_negative_jump_magnitude_three_endpoint_interval_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:31:51.70619+00:00
-- url     : https://prove2.me/submissions/4424e9b6-313f-4607-b697-c3c153cad914

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Actual original-source negative left-jump magnitude series is
exactly additive over any three ordered interval endpoints, even
with infinite jump activity; no compensation or Poisson model. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t r : ℝ≥0) (hst : s ≤ t) (htr : t ≤ r) :
    (∑' (v : ℝ≥0),
      if s < v ∧ v ≤ r then
        ENNReal.ofReal (Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      else 0) =
    (∑' (v : ℝ≥0),
      if s < v ∧ v ≤ t then
        ENNReal.ofReal (Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      else 0) +
    (∑' (v : ℝ≥0),
      if t < v ∧ v ≤ r then
        ENNReal.ofReal (Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      else 0) := by
  classical
  let j (v : ℝ≥0) : ℝ≥0∞ :=
    ENNReal.ofReal (Function.leftLim
      (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
  have hpoint (v : ℝ≥0) :
      (if s < v ∧ v ≤ r then j v else 0) =
        (if s < v ∧ v ≤ t then j v else 0) +
          (if t < v ∧ v ≤ r then j v else 0) := by
    by_cases hvt : v ≤ t
    · have hvr : v ≤ r := hvt.trans htr
      have hno : ¬ t < v := not_lt.mpr hvt
      by_cases hsv : s < v
      · simp [hsv, hvt, hvr, hno]
      · simp [hsv, hno]
    · have htv : t < v := lt_of_not_ge hvt
      have hsv : s < v := lt_of_le_of_lt hst htv
      by_cases hvr : v ≤ r
      · simp [hsv, hvt, hvr]
      · simp [hsv, hvt, hvr]
  change tsum (fun v : ℝ≥0 => if s < v ∧ v ≤ r then j v else 0) =
    tsum (fun v : ℝ≥0 => if s < v ∧ v ≤ t then j v else 0) +
      tsum (fun v : ℝ≥0 => if t < v ∧ v ≤ r then j v else 0)
  calc
    tsum (fun v : ℝ≥0 => if s < v ∧ v ≤ r then j v else 0) =
        tsum (fun v : ℝ≥0 =>
          (if s < v ∧ v ≤ t then j v else 0) +
            (if t < v ∧ v ≤ r then j v else 0)) := by
            apply tsum_congr
            intro v
            exact hpoint v
    _ = _ := ENNReal.tsum_add

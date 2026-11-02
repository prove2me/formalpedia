-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_source_negative_jump_series_interval_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:27:25.633026+00:00
-- url     : https://prove2.me/submissions/0d34dbfa-8ff5-4ca1-945d-8cf71af95c4b

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original source negative left-jump magnitudes have an exactly additive
series over consecutive intervals. This is pathwise, including infinite
activity, and does not identify any stochastic compensator or dividend jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∑' (u : ℝ≥0),
      if 0 < u ∧ u ≤ t then
        ENNReal.ofReal (Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0) =
    (∑' (u : ℝ≥0),
      if 0 < u ∧ u ≤ s then
        ENNReal.ofReal (Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0) +
    (∑' (u : ℝ≥0),
      if s < u ∧ u ≤ t then
        ENNReal.ofReal (Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0) := by
  classical
  let j (u : ℝ≥0) : ℝ≥0∞ :=
    ENNReal.ofReal (Function.leftLim
      (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
  have hpoint (u : ℝ≥0) :
      (if 0 < u ∧ u ≤ t then j u else 0) =
      (if 0 < u ∧ u ≤ s then j u else 0) +
        (if s < u ∧ u ≤ t then j u else 0) := by
    by_cases hus : u ≤ s
    · have hut : u ≤ t := hus.trans hst
      have hno : ¬ s < u := not_lt.mpr hus
      by_cases hu : 0 < u
      · simp [hu, hus, hut, hno]
      · simp [hu, hno]
    · have hsu : s < u := lt_of_not_ge hus
      have hu : 0 < u :=
        lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hsu
      by_cases hut : u ≤ t
      · simp [hu, hus, hsu, hut]
      · simp [hu, hus, hsu, hut]
  change tsum (fun u : ℝ≥0 =>
    if 0 < u ∧ u ≤ t then j u else 0) =
      tsum (fun u : ℝ≥0 => if 0 < u ∧ u ≤ s then j u else 0) +
        tsum (fun u : ℝ≥0 => if s < u ∧ u ≤ t then j u else 0)
  calc
    tsum (fun u : ℝ≥0 => if 0 < u ∧ u ≤ t then j u else 0) =
        tsum (fun u : ℝ≥0 =>
          (if 0 < u ∧ u ≤ s then j u else 0) +
            (if s < u ∧ u ≤ t then j u else 0)) := by
            apply tsum_congr
            intro u
            exact hpoint u
    _ = _ := ENNReal.tsum_add

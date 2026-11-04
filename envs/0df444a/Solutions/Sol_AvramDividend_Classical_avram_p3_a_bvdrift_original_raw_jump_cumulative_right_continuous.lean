-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:06:49.449814+00:00
-- url     : https://prove2.me/submissions/b6441fee-e810-4330-bb17-d1eba86e504d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_right

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual BV source cumulative signed negative-left-jump process
is right-continuous even when its infinite-horizon jump sum diverges. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Filter.Tendsto (fun s : ℝ≥0 => (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) (𝓝[>] t)
        (nhds (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
    with ω hω
  intro t
  let B : ℝ≥0 := t + 1
  let f (u : ℝ≥0) : ℝ :=
    if 0 < u ∧ u ≤ B then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
    else 0
  have hSum : Summable f :=
    (hω 0 B (show (0 : ℝ≥0) ≤ B from zero_le)).1
  have hSumAbs : Summable (fun u : ℝ≥0 => |f u|) := hSum.abs
  have hlim :
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then f u else 0) = (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by
    apply tsum_congr
    intro u
    by_cases hu : 0 < u ∧ u ≤ t
    · have hub : u ≤ B := hu.2.trans (by simp [B])
      simp [f, hu, hub]
    · simp [hu]
  have hB : t < B := by simp [B]
  have hevent :
      (fun s : ℝ≥0 =>
        ∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then f u else 0) =ᶠ[𝓝[>] t]
      (fun s : ℝ≥0 => (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) := by
    have hevs : ∀ᶠ s : ℝ≥0 in 𝓝[>] t, s < B := by
      have hh : ∀ᶠ s : ℝ≥0 in nhds t, s < B :=
        isOpen_Iio.mem_nhds hB
      exact hh.filter_mono nhdsWithin_le_nhds
    filter_upwards [hevs] with s hs
    apply tsum_congr
    intro u
    by_cases hu : 0 < u ∧ u ≤ s
    · have hub : u ≤ B := hu.2.trans (le_of_lt hs)
      simp [f, hu, hub]
    · simp [hu]
  have hbase :=
    avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_right f hSumAbs t
  rw [hlim] at hbase
  exact hbase.congr' hevent

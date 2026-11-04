-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:21:16.808056+00:00
-- url     : https://prove2.me/submissions/f2021902-21c0-4f15-b337-3877bf038f1b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_right_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original BV source drift residual after removing
its negative left-jump sum is right-continuous for every sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Filter.Tendsto (fun s : ℝ≥0 =>
        (((s : ℝ) * X.drift - X.X s ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))
        (𝓝[>] t)
        (nhds ((((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_jump_cumulative_right_continuous X hBV]
    with ω hright
  intro t
  have hX : Tendsto (fun s : ℝ≥0 => X.X s ω)
      (𝓝[>] t) (nhds (X.X t ω)) := by
    have hsubset : (Ioi t : Set ℝ≥0) ⊆ Ici t := by
      intro s hs
      exact Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hs))
    exact (X.rightCont ω t).mono_left (nhdsWithin_mono t hsubset)
  have htime : Tendsto (fun s : ℝ≥0 => (s : ℝ) * X.drift)
      (𝓝[>] t) (nhds ((t : ℝ) * X.drift)) :=
    ((NNReal.continuous_coe.mul continuous_const).tendsto t).mono_left
      nhdsWithin_le_nhds
  exact (htime.sub hX).sub (hright t)

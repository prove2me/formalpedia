-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:31:31.528199+00:00
-- url     : https://prove2.me/submissions/2473d9a1-f2cf-4bfb-b193-1e4ade643bb1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_left

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On the actual BV Levy source path, the cumulative raw real
negative-jump series has the strict-past jump sum as its left limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Function.leftLim (fun s : ℝ≥0 => (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) t =
        (∑' u : ℝ≥0, if 0 < u ∧ u < t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
    with ω hω
  intro t ht
  let f (u : ℝ≥0) : ℝ :=
    if 0 < u ∧ u ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
    else 0
  have hsum : Summable f := (hω 0 t (show (0 : ℝ≥0) ≤ t from zero_le)).1
  have hsumabs : Summable (fun u : ℝ≥0 => |f u|) := hsum.abs
  have hlimit :
      (∑' u : ℝ≥0, if 0 < u ∧ u < t then f u else 0) =
      (∑' u : ℝ≥0, if 0 < u ∧ u < t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by
    apply tsum_congr
    intro u
    by_cases hu : 0 < u ∧ u < t
    · have hut : u ≤ t := le_of_lt hu.2
      simp [f, hu, hu.1, hut]
    · simp [hu]
  have hnear (s : ℝ≥0) (hs : s < t) :
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then f u else 0) =
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by
    apply tsum_congr
    intro u
    by_cases hu : 0 < u ∧ u ≤ s
    · have hut : u ≤ t := hu.2.trans (le_of_lt hs)
      simp [f, hu, hu.1, hut]
    · simp [hu]
  have hevent :
      (fun s : ℝ≥0 => ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ s then f u else 0) =ᶠ[𝓝[<] t]
      (fun s : ℝ≥0 => (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) := by
    filter_upwards [(self_mem_nhdsWithin :
      ∀ᶠ s : ℝ≥0 in 𝓝[<] t, s < t)] with s hs
    exact hnear s hs
  have htendsto :=
    avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_left f hsumabs t ht
  rw [hlimit] at htendsto
  have hsource := htendsto.congr' hevent
  haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  exact leftLim_eq_of_tendsto hsource

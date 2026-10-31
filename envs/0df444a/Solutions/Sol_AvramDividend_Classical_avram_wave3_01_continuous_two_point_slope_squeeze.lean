-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_continuous_two_point_slope_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:01:37.292974+00:00
-- url     : https://prove2.me/submissions/0cbccc95-07e4-4558-8080-2719c818fe3d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set
open scoped Topology

/-- A continuous two-point slope envelope gives differentiability at
every positive argument with derivative equal to the envelope value. -/
theorem solution
    (f κ : ℝ → ℝ)
    (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (hslope : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b →
      min (κ a) (κ b) ≤ slope f a b ∧
        slope f a b ≤ max (κ a) (κ b)) :
    ∀ a : ℝ, 0 < a → HasDerivAt f (κ a) a := by
  intro a ha
  apply (hasDerivAt_iff_tendsto_slope).2
  have hκat : ContinuousAt κ a :=
    hκ.continuousAt (isOpen_Ioi.mem_nhds ha)
  have hκlim : Tendsto κ (𝓝[≠] a) (𝓝 (κ a)) :=
    hκat.tendsto.mono_left inf_le_left
  have hconst : Tendsto (fun _ : ℝ => κ a)
      (𝓝[≠] a) (𝓝 (κ a)) := tendsto_const_nhds
  have hlo : Tendsto (fun b : ℝ => min (κ a) (κ b))
      (𝓝[≠] a) (𝓝 (κ a)) := by
    simpa only [min_self] using hconst.min hκlim
  have hhi : Tendsto (fun b : ℝ => max (κ a) (κ b))
      (𝓝[≠] a) (𝓝 (κ a)) := by
    simpa only [max_self] using hconst.max hκlim
  have hpos : ∀ᶠ b : ℝ in 𝓝[≠] a, 0 < b := by
    exact Filter.Eventually.filter_mono inf_le_left
      (isOpen_Ioi.mem_nhds ha)
  have hne : ∀ᶠ b : ℝ in 𝓝[≠] a, a ≠ b := by
    have hmem : ∀ᶠ b : ℝ in 𝓝[≠] a,
        b ∈ ({a}ᶜ : Set ℝ) := self_mem_nhdsWithin
    filter_upwards [hmem] with b hb
    have hbn : b ≠ a := by simpa using hb
    exact hbn.symm
  have hboundLo : ∀ᶠ b : ℝ in 𝓝[≠] a,
      min (κ a) (κ b) ≤ slope f a b := by
    filter_upwards [hpos, hne] with b hb hn
    exact (hslope a b ha hb hn).1
  have hboundHi : ∀ᶠ b : ℝ in 𝓝[≠] a,
      slope f a b ≤ max (κ a) (κ b) := by
    filter_upwards [hpos, hne] with b hb hn
    exact (hslope a b ha hb hn).2
  exact Filter.Tendsto.squeeze' hlo hhi hboundLo hboundHi

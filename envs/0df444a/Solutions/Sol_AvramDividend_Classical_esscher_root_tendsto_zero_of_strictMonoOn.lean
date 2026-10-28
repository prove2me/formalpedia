-- Prove2me | solution 1 for AvramDividend.Classical.esscher_root_tendsto_zero_of_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:34:16.165038+00:00
-- url     : https://prove2.me/submissions/179f4096-0739-475d-a95f-58156f0a5baa

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Order.Monotone.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set

/-- Every positive inverse root approaches zero for a strictly increasing exponent. -/
theorem solution
    (g root : ℝ → ℝ)
    (hzero : g 0 = 0)
    (hmono : StrictMonoOn g (Ici (0 : ℝ)))
    (hpos : ∀ p : ℝ, 0 < p → 0 < root p)
    (hroot : ∀ p : ℝ, 0 < p → g (root p) = p) :
    Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact lt_trans ha (hpos p hp)
    · intro a ha
      have ha_mem : a ∈ Ici (0 : ℝ) := ha.le
      have hgpos : 0 < g a := by
        have hga := hmono (by simp : (0 : ℝ) ∈ Ici 0) ha_mem ha
        simpa only [hzero] using hga
      have hev : ∀ᶠ p : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), p < g a :=
        eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hgpos)
      filter_upwards [hev, self_mem_nhdsWithin] with p hp_lt hp
      by_contra hn
      have hle : a ≤ root p := le_of_not_gt hn
      have hroot_mem : root p ∈ Ici (0 : ℝ) := (hpos p hp).le
      have hga : g a ≤ g (root p) :=
        hmono.monotoneOn ha_mem hroot_mem hle
      rw [hroot p hp] at hga
      exact (not_lt_of_ge hga) hp_lt
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact hpos p hp

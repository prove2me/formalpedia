-- Prove2me | solution 1 for AvramDividend.Classical.chat04_rightContinuous_masked_reward_of_zero_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:39:35.495199+00:00
-- url     : https://prove2.me/submissions/e8a8d63c-5db0-449d-9e64-e49b13be2fe9

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-- A right-continuous reward stays right-continuous after killing when any
    possible survival transition occurs at zero reward. -/
theorem solution
    (g : NNReal → ℝ) (S : NNReal → Prop) [DecidablePred S] (t : NNReal)
    (hg : ContinuousWithinAt g (Set.Ici t) t)
    (hsafe : S t → g t ≠ 0 → ∀ᶠ s in 𝓝[Set.Ici t] t, S s)
    (hunsafe : ¬ S t → ∀ᶠ s in 𝓝[Set.Ici t] t, ¬ S s) :
    ContinuousWithinAt (fun s => if S s then g s else 0) (Set.Ici t) t := by
  classical
  change Tendsto (fun s => if S s then g s else 0)
    (𝓝[Set.Ici t] t) (𝓝 (if S t then g t else 0))
  by_cases ht : S t
  · by_cases hz : g t = 0
    · have hzero : Tendsto g (𝓝[Set.Ici t] t) (𝓝 (0 : ℝ)) := by
        have hgt : Tendsto g (𝓝[Set.Ici t] t) (𝓝 (g t)) := hg
        simpa [hz] using hgt
      have hmasked : Tendsto (fun s => if S s then g s else 0)
          (𝓝[Set.Ici t] t) (𝓝 (0 : ℝ)) :=
        Filter.Tendsto.if' hzero tendsto_const_nhds
      simpa [ht, hz] using hmasked
    · have heq : g =ᶠ[𝓝[Set.Ici t] t]
          (fun s => if S s then g s else 0) := by
        filter_upwards [hsafe ht hz] with s hs
        simp [hs]
      have hgt : Tendsto g (𝓝[Set.Ici t] t) (𝓝 (g t)) := hg
      simpa [ht] using hgt.congr' heq
  · have heq : (fun _ : NNReal => (0 : ℝ)) =ᶠ[𝓝[Set.Ici t] t]
        (fun s => if S s then g s else 0) := by
      filter_upwards [hunsafe ht] with s hs
      simp [hs]
    have hconst : Tendsto (fun _ : NNReal => (0 : ℝ))
        (𝓝[Set.Ici t] t) (𝓝 (0 : ℝ)) := tendsto_const_nhds
    simpa [ht] using hconst.congr' heq

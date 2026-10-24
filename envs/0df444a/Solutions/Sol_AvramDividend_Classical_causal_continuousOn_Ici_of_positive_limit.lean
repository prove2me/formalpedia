-- Prove2me | solution 1 for AvramDividend.Classical.causal_continuousOn_Ici_of_positive_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:05:24.850406+00:00
-- url     : https://prove2.me/submissions/b4cd906a-ceee-4598-93b6-5c59302dc574

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.ContinuousOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter
open scoped Topology

theorem solution
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (hlim : Tendsto f (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds (f 0))) :
    ContinuousOn f (Ici (0 : ℝ)) := by
  intro x hx
  change (0 : ℝ) ≤ x at hx
  rcases eq_or_lt_of_le hx with hzero | hpos
  · subst x
    have hlim' : Tendsto f (nhdsWithin (0 : ℝ) (Ici (0 : ℝ)))
        (nhds (f 0)) := by
      intro U hU
      have hev : ∀ᶠ y in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)), f y ∈ U :=
        hlim.eventually hU
      change ∀ᶠ y in nhdsWithin (0 : ℝ) (Ici (0 : ℝ)), f y ∈ U
      rw [eventually_nhdsWithin_iff] at hev ⊢
      filter_upwards [hev] with y hy
      intro hy0
      change (0 : ℝ) ≤ y at hy0
      rcases eq_or_lt_of_le hy0 with hz | hp
      · subst y
        exact mem_of_mem_nhds hU
      · apply hy
        change (0 : ℝ) < y
        exact hp
    exact hlim'
  · have hxe : x ∈ Ioi (0 : ℝ) := hpos
    have hat : ContinuousAt f x :=
      hf.continuousAt (isOpen_Ioi.mem_nhds hxe)
    exact hat.continuousWithinAt

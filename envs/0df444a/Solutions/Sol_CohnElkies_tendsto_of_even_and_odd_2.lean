-- Prove2me | solution 2 for CohnElkies.tendsto_of_even_and_odd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:16.006571+00:00
-- url     : https://prove2.me/submissions/f0ecfc49-dffa-423d-a9bd-5a0afbb99b3a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology


theorem solution {X : Type*} [TopologicalSpace X]
    {f : ℕ → X} {x : X}
    (heven : Tendsto (fun k : ℕ => f (2 * k)) atTop (nhds x))
    (hodd : Tendsto (fun k : ℕ => f (2 * k + 1)) atTop (nhds x)) :
    Tendsto f atTop (nhds x) := by
  rw [tendsto_nhds]
  intro s hs hxs
  have he := (tendsto_nhds.mp heven) s hs hxs
  have ho := (tendsto_nhds.mp hodd) s hs hxs
  rw [Filter.mem_atTop_sets] at he ho ⊢
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := ho
  refine ⟨2 * (a + b) + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact ha k (by omega)
  · exact hb k (by omega)


-- Prove2me | solution 1 for CohnElkies.tendsto_of_even_and_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/4174efcf-ac45-44e7-860b-a610754314e5

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
namespace CohnElkies
theorem _root_.solution {X : Type*} [TopologicalSpace X]
    {f : ℕ → X} {x : X}
    (heven : Tendsto (fun k : ℕ => f (2 * k)) atTop (nhds x))
    (hodd : Tendsto (fun k : ℕ => f (2 * k + 1)) atTop (nhds x)) :
    Tendsto f atTop (nhds x) := by
  refine Filter.tendsto_iff_forall_eventually_mem.2 ?_
  intro s hs
  obtain ⟨Ne, hNe⟩ :=
    Filter.eventually_atTop.1 (heven.eventually hs)
  obtain ⟨No, hNo⟩ :=
    Filter.eventually_atTop.1 (hodd.eventually hs)
  refine Filter.eventually_atTop.2
    ⟨2 * max Ne No + 1, ?_⟩
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp he
    apply hNe
    omega
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp ho
    apply hNo
    omega
end CohnElkies

-- Prove2me | solution 1 for Csg.CSG.exists_forall_le_add_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:01:58.533878+00:00
-- url     : https://prove2.me/submissions/943cf52f-a6aa-47ce-b955-7e6b410050ad

import Definitions.Def_Csg_ReachOp
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder
import Definitions.Def_Csg_ReachConverge

set_option autoImplicit true
open Csg
open Csg.CSG
open OmegaCompletePartialOrder Filter Topology
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
omit [Fintype S]
namespace Csg.CSG
theorem _root_.solution [Finite S] {g : S → ℝ} {d : ℕ → S → ℝ}
    (htendsto : ∀ s', Tendsto (fun n => d n s') atTop (𝓝 (g s'))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ∀ n ≥ N, ∀ s', g s' ≤ d n s' + δ := by
  have h1 : ∀ s', ∀ᶠ n in atTop, g s' - δ < d n s' := fun s' =>
    (tendsto_order.mp (htendsto s')).1 (g s' - δ) (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_all.mpr h1)
  exact ⟨N, fun n hn s' => by linarith [hN n hn s']⟩
end Csg.CSG

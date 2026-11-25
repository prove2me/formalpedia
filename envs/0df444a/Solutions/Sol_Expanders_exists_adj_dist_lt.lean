-- Prove2me | solution 1 for Expanders.exists_adj_dist_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:29:15.252372+00:00
-- url     : https://prove2.me/submissions/4b249e9c-a8b1-4fd0-8631-773884437119

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} {G : SimpleGraph V}
namespace Expanders
theorem _root_.solution {u v : V} (huv : G.Reachable u v) (h0 : G.dist u v ≠ 0) :
    ∃ w, G.Adj v w ∧ G.Reachable u w ∧ G.dist u w + 1 ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
  have hl : p.reverse.length = G.dist u v := by simp [hp]
  generalize p.reverse = q at hl
  cases q with
  | nil => simp at h0
  | cons hadj q =>
    refine ⟨_, hadj, ⟨q.reverse⟩, ?_⟩
    have := dist_le q.reverse
    simp at hl this; omega
end Expanders

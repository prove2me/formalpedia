-- Prove2me | solution 1 for Erdos146.CompactnessConjecture.free_map_of_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T04:54:56.31302+00:00
-- url     : https://prove2.me/submissions/c9db4cd8-a7db-4f78-8ae7-158ace53ae79

import Definitions.Def_erdos146_core2
import Mathlib.Combinatorics.SimpleGraph.Copy

open Erdos146
open SimpleGraph

theorem solution
    {U V W : Type*}
    (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {host : SimpleGraph V}
    (embedding : V ↪ W)
    (hfree : forbidden.Free host) :
    forbidden.Free (host.map embedding) := by
  classical
  rintro ⟨copy⟩
  have hpreimage (u : U) :
      ∃ v : V, embedding v = copy u := by
    obtain ⟨w, huw⟩ := hneighbors u
    have hadj := copy.toHom.map_rel huw
    change (host.map embedding).Adj (copy u) (copy w) at hadj
    obtain ⟨v, _, _, hv, _⟩ :=
      (SimpleGraph.map_adj embedding host _ _).mp hadj
    exact ⟨v, hv⟩
  let lift : U → V := fun u => Classical.choose (hpreimage u)
  have hlift (u : U) : embedding (lift u) = copy u :=
    Classical.choose_spec (hpreimage u)
  apply hfree
  refine ⟨⟨⟨lift, ?_⟩, ?_⟩⟩
  · intro u v huv
    have hadj := copy.toHom.map_rel huv
    change (host.map embedding).Adj (copy u) (copy v) at hadj
    rw [← hlift u, ← hlift v] at hadj
    exact SimpleGraph.map_adj_apply.mp hadj
  · intro u v huv
    change lift u = lift v at huv
    apply copy.injective
    change copy u = copy v
    rw [← hlift u, ← hlift v]
    exact congrArg embedding huv

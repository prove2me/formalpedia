-- Prove2me | solution 1 for CompactnessConjecture.free_map_of_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/aadcb468-0369-4326-b1a7-bd7d37ce4122

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
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
end CompactnessConjecture

-- Prove2me | solution 1 for C6BipartiteDomination.collective_exchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:40:16.114008+00:00
-- url     : https://prove2.me/submissions/a8a26699-9805-4ab3-9cd9-c6189a051736

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic
import Definitions.Def_C6BipartiteDomination_Basic

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X Y : Finset V}
    (hcover : ∀ ⦃v⦄, Responsible G D X v → v ∈ Y ∨ ∃ y ∈ Y, G.Adj y v)
    (hbip : IsBipartiteOn G ((D \ X) ∪ Y)) :
    IsBipartiteDominatingSet G ((D \ X) ∪ Y) := by
  refine ⟨?_, hbip⟩
  intro v hv
  by_cases hresp : Responsible G D X v
  · rcases hcover hresp with hy | ⟨y, hy, hadj⟩
    · exact (hv (Finset.mem_union_right (D \ X) hy)).elim
    · exact ⟨y, Finset.mem_union_right _ hy, hadj⟩
  · by_cases hret : v ∈ D \ X
    · exact (hv (Finset.mem_union_left Y hret)).elim
    · have hnot : ¬ ∀ u ∈ D \ X, ¬ G.Adj u v := by
        intro h
        exact hresp ⟨hret, h⟩
      push Not at hnot
      obtain ⟨u, hu, hadj⟩ := hnot
      exact ⟨u, Finset.mem_union_left Y hu, hadj⟩
end C6BipartiteDomination

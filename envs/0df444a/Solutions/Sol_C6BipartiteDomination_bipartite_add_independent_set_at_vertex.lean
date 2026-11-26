-- Prove2me | solution 1 for C6BipartiteDomination.bipartite_add_independent_set_at_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:59.004806+00:00
-- url     : https://prove2.me/submissions/97b199f7-300d-4cff-965b-d6f2be1a0f8b

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {S U : Finset V} {w : V}
    (hS : IsBipartiteOn G S) (hwS : w ∈ S)
    (hU : Independent G U) (hwU : w ∉ U)
    (hdisj : Disjoint S U)
    (hboundary : ∀ ⦃u v⦄, u ∈ U → v ∈ S → G.Adj u v → v = w) :
    IsBipartiteOn G (S ∪ U) := by
  classical
  rcases hS with ⟨c, hc⟩
  refine ⟨fun v => if v ∈ U then !c w else c v, ?_⟩
  intro a b ha hb hab
  rcases Finset.mem_union.mp ha with haS | haU
  · rcases Finset.mem_union.mp hb with hbS | hbU
    · have haNotU : a ∉ U := by
        intro h
        exact (Finset.disjoint_left.mp hdisj haS h).elim
      have hbNotU : b ∉ U := by
        intro h
        exact (Finset.disjoint_left.mp hdisj hbS h).elim
      simpa [haNotU, hbNotU] using hc haS hbS hab
    · have hvEq : a = w := hboundary hbU haS hab.symm
      subst a
      have haNotU : w ∉ U := hwU
      simp [haNotU, hbU]
  · rcases Finset.mem_union.mp hb with hbS | hbU
    · have hvEq : b = w := hboundary haU hbS hab
      subst b
      have hbNotU : w ∉ U := hwU
      simp [haU, hbNotU]
    · exact (hU haU hbU hab).elim
end C6BipartiteDomination

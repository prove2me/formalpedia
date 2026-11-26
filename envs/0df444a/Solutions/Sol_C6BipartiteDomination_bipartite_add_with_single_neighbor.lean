-- Prove2me | solution 1 for C6BipartiteDomination.bipartite_add_with_single_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:56.441795+00:00
-- url     : https://prove2.me/submissions/95332d88-72d6-4d49-9bc7-4180f6b8a140

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {S : Finset V} {q u : V}
    (hS : IsBipartiteOn G S) (hu : u ∈ S) (hqu : G.Adj q u)
    (hqS : q ∉ S)
    (honly : ∀ v ∈ S, G.Adj q v → v = u) :
    IsBipartiteOn G (S ∪ {q}) := by
  classical
  rcases hS with ⟨c, hc⟩
  refine ⟨fun v => if v = q then !c u else c v, ?_⟩
  intro a b ha hb hab
  rcases Finset.mem_union.mp ha with haS | haq
  · rcases Finset.mem_union.mp hb with hbS | hbq
    · have haq' : a ≠ q := fun h => hqS (h ▸ haS)
      have hbq' : b ≠ q := fun h => hqS (h ▸ hbS)
      simpa [haq', hbq'] using hc haS hbS hab
    · have hbEq : b = q := Finset.mem_singleton.mp hbq
      subst b
      have haq' : a ≠ q := fun h => hqS (h ▸ haS)
      have hau : a = u := honly a haS hab.symm
      subst a
      simp [haq']
  · have haEq : a = q := Finset.mem_singleton.mp haq
    subst a
    rcases Finset.mem_union.mp hb with hbS | hbq
    · have hbq' : b ≠ q := fun h => hqS (h ▸ hbS)
      have hbu : b = u := honly b hbS hab
      subst b
      simp [hbq']
    · have hbEq : b = q := Finset.mem_singleton.mp hbq
      subst b
      exact (G.irrefl hab).elim
end C6BipartiteDomination

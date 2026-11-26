-- Prove2me | solution 1 for C6BipartiteDomination.bipartite_add_of_uniform_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:25.857971+00:00
-- url     : https://prove2.me/submissions/dd19f206-30d6-42be-8f43-f21e22dabd70

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {B S : Finset V} {w : V}
    (hSB : S ⊆ B) (hwS : w ∉ S)
    (c : V → Bool)
    (hc : ∀ ⦃u v⦄, u ∈ B → v ∈ B → G.Adj u v → c u ≠ c v)
    (c₀ : Bool)
    (huniform : ∀ v ∈ S, G.Adj w v → c v = c₀) :
    IsBipartiteOn G (S ∪ {w}) := by
  classical
  refine ⟨fun v => if v = w then !c₀ else c v, ?_⟩
  intro u v hu hv hadj
  rcases Finset.mem_union.mp hu with huS | huW
  · rcases Finset.mem_union.mp hv with hvS | hvW
    · have huNe : u ≠ w := fun h => hwS (h ▸ huS)
      have hvNe : v ≠ w := fun h => hwS (h ▸ hvS)
      simpa [huNe, hvNe] using hc (hSB huS) (hSB hvS) hadj
    · have hvEq : v = w := Finset.mem_singleton.mp hvW
      subst v
      have huNe : u ≠ w := fun h => hwS (h ▸ huS)
      have hc₀ := huniform u huS hadj.symm
      simp [huNe, hc₀]
  · have huEq : u = w := Finset.mem_singleton.mp huW
    subst u
    rcases Finset.mem_union.mp hv with hvS | hvW
    · have hvNe : v ≠ w := fun h => hwS (h ▸ hvS)
      have hc₀ := huniform v hvS hadj
      simp [hvNe, hc₀]
    · have hvEq : v = w := Finset.mem_singleton.mp hvW
      subst v
      exact (G.irrefl hadj).elim
end C6BipartiteDomination

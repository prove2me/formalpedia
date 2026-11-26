-- Prove2me | solution 1 for C6BipartiteDomination.repair_of_uniform_remaining_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:48:14.1288+00:00
-- url     : https://prove2.me/submissions/0e7b854c-c40d-4bc4-a1bb-ec770d04c488

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
import Theorems.Thm_C6BipartiteDomination_bipartite_add_of_uniform_neighbors
import Theorems.Thm_C6BipartiteDomination_mem_BPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} {w u : V}
    (hwD : w ∉ D) (hu : u ∈ BPart G D) (hwu : G.Adj w u)
    (c : V → Bool)
    (hc : ∀ ⦃x y⦄, x ∈ BPart G D → y ∈ BPart G D →
      G.Adj x y → c x ≠ c y)
    (c₀ : Bool)
    (huniform : ∀ v ∈ (BPart G D).erase u, G.Adj w v → c v = c₀) :
    IsRepairVertex G D w u := by
  have hwErase : w ∉ (BPart G D).erase u := by
    intro hw
    exact hwD ((mem_BPart G D w).mp (Finset.erase_subset u _ hw) |>.1)
  have hbip := bipartite_add_of_uniform_neighbors G
    (Finset.erase_subset u (BPart G D)) hwErase c hc c₀ huniform
  exact ⟨hu, hwu, hbip⟩
end C6BipartiteDomination

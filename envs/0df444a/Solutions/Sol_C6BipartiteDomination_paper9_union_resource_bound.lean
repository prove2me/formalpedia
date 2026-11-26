-- Prove2me | solution 1 for C6BipartiteDomination.paper9_union_resource_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:54:03.474632+00:00
-- url     : https://prove2.me/submissions/a2ba7a79-0e4f-4757-9683-1399dea51752

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D T L : Finset V} {u : V}
    (hT : T ⊆ (SPart G D).filter (fun q => G.Adj u q))
    (hL : L ⊆ (SPart G D).filter (fun q => G.Adj u q))
    (hdisj : Disjoint T L) :
    T.card + L.card ≤ sCharge G D u := by
  have hsub : T ∪ L ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    intro q hq
    rcases Finset.mem_union.mp hq with hqT | hqL
    · exact hT hqT
    · exact hL hqL
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  simpa [sCharge, degreeTo] using hcard
end C6BipartiteDomination

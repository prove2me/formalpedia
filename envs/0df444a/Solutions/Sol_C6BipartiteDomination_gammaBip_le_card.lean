-- Prove2me | solution 1 for C6BipartiteDomination.gammaBip_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:05.223554+00:00
-- url     : https://prove2.me/submissions/e3145052-3a53-4dcb-9576-9c89f98309ea

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace C6BipartiteDomination
theorem _root_.solution (G : SimpleGraph V) {D : Finset V}
    (hD : IsBipartiteDominatingSet G D) :
    gammaBip G ≤ D.card := by
  apply Nat.find_min' (exists_bipartite_dominating_card G)
  exact ⟨D, hD, rfl⟩
end C6BipartiteDomination

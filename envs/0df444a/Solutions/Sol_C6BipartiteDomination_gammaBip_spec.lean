-- Prove2me | solution 1 for C6BipartiteDomination.gammaBip_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:04.644925+00:00
-- url     : https://prove2.me/submissions/513ee30d-2c15-4885-8ed0-3ca563beadde

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace C6BipartiteDomination
theorem _root_.solution (G : SimpleGraph V) :
    ∃ D : Finset V,
      IsBipartiteDominatingSet G D ∧ D.card = gammaBip G := by
  rcases Nat.find_spec (exists_bipartite_dominating_card G) with
    ⟨D, hD, hcard⟩
  exact ⟨D, hD, by simpa [gammaBip] using hcard⟩
end C6BipartiteDomination

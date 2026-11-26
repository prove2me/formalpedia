-- Prove2me | solution 1 for C6BipartiteDomination.corona_leaf_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:32.726022+00:00
-- url     : https://prove2.me/submissions/6cec96c0-63f1-4de5-baff-b3d85afd1d47

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_corona_leaf_neighbor_finset

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution (i : Fin 5) (p : Fin 2) :
    degreeTo coronaGraph Finset.univ (Sum.inr (i, p)) = 1 := by
  classical
  unfold degreeTo
  rw [corona_leaf_neighbor_finset]
  simp
end C6BipartiteDomination

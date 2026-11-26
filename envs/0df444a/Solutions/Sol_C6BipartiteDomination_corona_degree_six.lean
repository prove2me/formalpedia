-- Prove2me | solution 1 for C6BipartiteDomination.corona_degree_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:09.95082+00:00
-- url     : https://prove2.me/submissions/1a063d1a-3099-45b0-a037-e873b0ec6dd1

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_corona_core_degree

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution :
    ∃ v, degreeTo coronaGraph Finset.univ v = 6 := by
  refine ⟨Sum.inl 0, ?_⟩
  exact corona_core_degree 0
end C6BipartiteDomination

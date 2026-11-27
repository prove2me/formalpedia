-- Prove2me | solution 1 for C6BipartiteDomination.corona_core_unselected_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:27.591941+00:00
-- url     : https://prove2.me/submissions/2d981269-8814-431a-a1d8-7b3edd489917

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset CoronaVertex} :
    (coronaSelectedCore D).card + (coronaUnselectedCore D).card = 5 := by
  classical
  have h := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (coronaSelectedCore D))
  have h' : (coronaUnselectedCore D).card +
      (coronaSelectedCore D).card = 5 := by
    simpa [coronaUnselectedCore] using h
  omega
end C6BipartiteDomination

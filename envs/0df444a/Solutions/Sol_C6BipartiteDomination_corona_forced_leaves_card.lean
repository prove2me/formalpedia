-- Prove2me | solution 1 for C6BipartiteDomination.corona_forced_leaves_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:09.348663+00:00
-- url     : https://prove2.me/submissions/3650d745-906d-46a0-98fc-b1e974582a37

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset CoronaVertex) :
    (coronaForcedLeaves D).card =
      (coronaUnselectedCore D).card * 2 := by
  classical
  unfold coronaForcedLeaves
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_product]
  · intro p q h
    exact Sum.inr.inj h
end C6BipartiteDomination

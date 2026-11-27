-- Prove2me | solution 1 for C6BipartiteDomination.corona_selected_core_vertices_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:04.723626+00:00
-- url     : https://prove2.me/submissions/cd10c2cd-2acd-40b9-96f6-0f49b5378594

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset CoronaVertex) :
    (coronaSelectedCoreVertices D).card = (coronaSelectedCore D).card := by
  classical
  unfold coronaSelectedCoreVertices
  apply Finset.card_image_of_injective
  intro i j h
  exact Sum.inl.inj h
end C6BipartiteDomination

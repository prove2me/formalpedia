-- Prove2me | solution 1 for C6BipartiteDomination.gammaBip_minimum_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:40.99046+00:00
-- url     : https://prove2.me/submissions/3591dda9-5304-40a8-8c45-f2e2f8d784a6

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_gammaBip_spec
import Theorems.Thm_C6BipartiteDomination_gammaBip_le_card

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace C6BipartiteDomination
theorem _root_.solution (G : SimpleGraph V) :
    ∃ D : Finset V,
      MinimumBipartiteDominatingSet G D ∧ D.card = gammaBip G := by
  obtain ⟨D, hD, hcard⟩ := gammaBip_spec G
  refine ⟨D, ⟨hD, ?_⟩, hcard⟩
  intro E hE
  have hgamma := gammaBip_le_card G hE
  omega
end C6BipartiteDomination

-- Prove2me | solution 1 for C6BipartiteDomination.corona_gamma_eq_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:10.795638+00:00
-- url     : https://prove2.me/submissions/7e4b2613-f149-4379-ae8c-315698a945b4

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_corona_every_bipartite_dominating_set_card_ge_eight
import Theorems.Thm_C6BipartiteDomination_gammaBip_spec
import Theorems.Thm_C6BipartiteDomination_gammaBip_le_card
import Theorems.Thm_C6BipartiteDomination_coronaWitness_card
import Theorems.Thm_C6BipartiteDomination_coronaWitness_isBipartiteDominating


set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace C6BipartiteDomination
theorem _root_.solution : gammaBip coronaGraph = 8 := by
  have hUpper : gammaBip coronaGraph ≤ 8 := by
    calc
      gammaBip coronaGraph ≤ coronaWitness.card :=
        gammaBip_le_card coronaGraph coronaWitness_isBipartiteDominating
      _ = 8 := coronaWitness_card
  obtain ⟨D, hD, hcard⟩ := gammaBip_spec coronaGraph
  have hLower : 8 ≤ gammaBip coronaGraph := by
    rw [← hcard]
    exact corona_every_bipartite_dominating_set_card_ge_eight hD
  omega
end C6BipartiteDomination

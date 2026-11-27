-- Prove2me | solution 1 for C6BipartiteDomination.corona_has_no_isolates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:01.270915+00:00
-- url     : https://prove2.me/submissions/fccc0612-e6b4-4e31-b34c-cb4727609369

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_corona_core_degree
import Theorems.Thm_C6BipartiteDomination_corona_leaf_degree

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution : HasNoIsolatedVertices coronaGraph := by
  intro v
  have hpos : 0 < degreeTo coronaGraph Finset.univ v := by
    cases v with
    | inl i => rw [corona_core_degree]; omega
    | inr p => rw [corona_leaf_degree]; omega
  have hne : (Finset.univ.filter (fun u => coronaGraph.Adj v u)).Nonempty := by
    apply Finset.card_pos.mp
    simpa [degreeTo] using hpos
  obtain ⟨u, hu⟩ := hne
  exact ⟨u, (Finset.mem_filter.mp hu).2⟩
end C6BipartiteDomination

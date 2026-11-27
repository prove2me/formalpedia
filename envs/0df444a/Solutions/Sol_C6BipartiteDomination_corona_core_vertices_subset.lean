-- Prove2me | solution 1 for C6BipartiteDomination.corona_core_vertices_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:18.887474+00:00
-- url     : https://prove2.me/submissions/5313a793-13d7-448b-b23c-bcf0f9d88cc6

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset CoronaVertex} :
    coronaSelectedCoreVertices D ⊆ D := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  exact (Finset.mem_filter.mp hi).2
end C6BipartiteDomination

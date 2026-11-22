-- Prove2me | solution 2 for GES.coherent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:14:52.971183+00:00
-- url     : https://prove2.me/submissions/a489a4ab-4c8c-4b00-81b5-9430f3dc14e4

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_General_Stable
import Mathlib.Data.Set.Lattice
import Definitions.Def_EventStructures_Stable_Basic

set_option autoImplicit true
open ConfFamily
variable {L : Type*}
namespace GES
theorem _root_.solution (G : GES L) : Coherent G.toFamily := by
  intro S z hS hz hsub
  refine ⟨fun X hX => hz.1 X (hX.trans (Set.sUnion_subset hsub)), ?_⟩
  rintro e ⟨m, hm, hem⟩
  obtain ⟨n, hn⟩ := (hS m hm).2 e hem
  exact ⟨n, GES.secApprox_mono_set (Set.subset_sUnion_of_mem hm) n hn⟩
end GES

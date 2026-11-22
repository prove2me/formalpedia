-- Prove2me | solution 1 for CCS.pmapSet_pfx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:41.413746+00:00
-- url     : https://prove2.me/submissions/49cee6ca-19ff-4aa2-8855-63c0bb5808d8

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics

set_option autoImplicit true
open PES Configuration ConfFamily
open CCS
variable {Name : Type*}
variable {Name : Type*}
variable {E F : SES (Action Name)} {α : Action Name}
namespace CCS
theorem _root_.solution (s : Set (Option E.Event)) :
    GES.pmapSet (G := (pfx α E).toGES) (H := E.toGES) id s = {z | some z ∈ s} := by
  refine Set.Subset.antisymm ?_ fun z hz => ⟨some z, hz, rfl⟩
  rintro z ⟨u, hu, hev⟩
  exact (hev ▸ hu : some z ∈ s)
end CCS

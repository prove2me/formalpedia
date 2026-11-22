-- Prove2me | solution 1 for CCS.pfx_none_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:57.691958+00:00
-- url     : https://prove2.me/submissions/554d003c-aab1-4770-86d3-747a363cfcd1

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
import Theorems.Thm_GES_exists_enabling


set_option autoImplicit true
open PES Configuration ConfFamily
open CCS
variable {Name : Type*}
variable {Name : Type*}
variable {E F : SES (Action Name)} {α : Action Name}
namespace CCS
theorem _root_.solution {c : Set (Option E.Event)}
    (hc : (pfx α E).toGES.isConf c) {z : E.Event} (hz : some z ∈ c) : none ∈ c := by
  obtain ⟨Y, hen, hYc⟩ := GES.exists_enabling hc hz
  exact hYc hen.1
end CCS

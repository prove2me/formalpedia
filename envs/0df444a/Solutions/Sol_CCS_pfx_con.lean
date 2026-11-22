-- Prove2me | solution 1 for CCS.pfx_con
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:10:38.194284+00:00
-- url     : https://prove2.me/submissions/3020bf67-b118-46d0-8675-0d8f1aed1b3d

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
theorem _root_.solution {c : Set (Option E.Event)} (h : (pfx α E).toGES.Consistent c) :
    E.toGES.Consistent {z | some z ∈ c} := by
  classical
  intro V hV
  refine h (V.image some) (fun u hu => ?_) V fun v hv => ?_
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact hV (by exact_mod_cast hv)
  · have : some v ∈ V.image some := Finset.mem_image.mpr ⟨v, by exact_mod_cast hv, rfl⟩
    exact_mod_cast this
end CCS

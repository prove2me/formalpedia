-- Prove2me | solution 1 for CCS.sum_con_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:10:40.340417+00:00
-- url     : https://prove2.me/submissions/08a6046c-e0d7-4405-9ae7-3b3596e5fa9f

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
theorem _root_.solution {c : Set (E.Event ⊕ F.Event)} (h : (sum E F).toGES.Consistent c) :
    F.toGES.Consistent {z | Sum.inr z ∈ c} := by
  classical
  intro V hV
  refine (h ((V.image Sum.inr : Finset (E.Event ⊕ F.Event))) fun u hu => ?_).2.2 V fun v hv => ?_
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact hV (by exact_mod_cast hv)
  · have : Sum.inr v ∈ (V.image Sum.inr : Finset (E.Event ⊕ F.Event)) :=
      Finset.mem_image.mpr ⟨v, by exact_mod_cast hv, rfl⟩
    exact_mod_cast this
end CCS

-- Prove2me | solution 1 for CCS.sum_con_L
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:10:38.656495+00:00
-- url     : https://prove2.me/submissions/d061063b-1772-4c84-8f88-948f2ba4d8c4

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
    E.toGES.Consistent {z | Sum.inl z ∈ c} := by
  classical
  intro V hV
  refine (h ((V.image Sum.inl : Finset (E.Event ⊕ F.Event))) fun u hu => ?_).2.1 V fun v hv => ?_
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact hV (by exact_mod_cast hv)
  · have : Sum.inl v ∈ (V.image Sum.inl : Finset (E.Event ⊕ F.Event)) :=
      Finset.mem_image.mpr ⟨v, by exact_mod_cast hv, rfl⟩
    exact_mod_cast this
end CCS

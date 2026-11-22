-- Prove2me | solution 1 for CCS.restrict_con
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:10:41.839594+00:00
-- url     : https://prove2.me/submissions/801845ef-cd44-4c56-bb47-5fddf6ccdb42

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
theorem _root_.solution {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
    (h : (restrict E).toGES.Consistent c) :
    E.toGES.Consistent {y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ c} := by
  classical
  intro V hV
  have hvis : ∀ v ∈ V, (E.label v).strip.isSome = true :=
    fun v hv => (hV (show v ∈ (V : Set E.Event) by exact_mod_cast hv)).choose
  refine h (V.attach.image fun v => ⟨v.1, hvis v.1 v.2⟩) (fun u hu => ?_) V fun v hv => ?_
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact (hV (show v.1 ∈ (V : Set E.Event) by exact_mod_cast v.2)).choose_spec
  · refine ⟨hvis v (by exact_mod_cast hv), ?_⟩
    have hmem : (⟨v, hvis v (by exact_mod_cast hv)⟩ : (restrict E).Event) ∈
        V.attach.image (fun z => (⟨z.1, hvis z.1 z.2⟩ : (restrict E).Event)) :=
      Finset.mem_image.mpr ⟨⟨v, by exact_mod_cast hv⟩, Finset.mem_attach _ _, rfl⟩
    exact_mod_cast hmem
end CCS

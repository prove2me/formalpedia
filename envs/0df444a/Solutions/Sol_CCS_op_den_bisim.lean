-- Prove2me | solution 1 for CCS.op_den_bisim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:23:19.97945+00:00
-- url     : https://prove2.me/submissions/0e00465e-acea-4668-8061-94e9780791f0

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
import Theorems.Thm_CCS_resid_empty
import Theorems.Thm_CCS_den_to_op
import Theorems.Thm_CCS_op_to_den
import Theorems.Thm_Bisimilar_symm
import Theorems.Thm_CCS_Action_strip_map
import Theorems.Thm_CCS_Label_co_co
import Theorems.Thm_CCS_Label_strip_map
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_GES_toFamily_Config
import Theorems.Thm_GES_toFamily_Event
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_toFamily_Config
import Theorems.Thm_PES_toFamily_Event
import Theorems.Thm_SES_toFamily_Config
attribute [local simp] CCS.Action.strip_map
attribute [local simp] CCS.Label.co_co
attribute [local simp] CCS.Label.strip_map
attribute [local simp] GES.toFamily_Config
attribute [local simp] GES.toFamily_Event
attribute [local simp] PES.enables_iff
attribute [local simp] PES.toFamily_Config
attribute [local simp] PES.toFamily_Event
attribute [local simp] SES.toFamily_Config


attribute [local simp] CCS.resid_empty

set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}
namespace CCS
theorem _root_.solution (P : Process Name) : Bisimilar (opLTSI P) (denLTSI P) := by
  refine ⟨fun Q c => Q = resid P c.1, (resid_empty P).symm, ?_, ?_⟩
  · rintro Q c α Q' rfl hstep
    obtain ⟨e, hins, hfr, hlbl, hQ⟩ := op_to_den P c.1 α Q' c.2 hstep
    exact ⟨⟨c.1 ∪ {e}, hins⟩, ⟨e, ⟨c.2, hins⟩, hfr, hlbl, rfl⟩, hQ⟩
  · rintro Q c α c' rfl ⟨e, hen, hfr, hlbl, htgt⟩
    refine ⟨resid P c'.1, ?_, rfl⟩
    rw [htgt, ← hlbl]
    exact den_to_op P c.1 e c.2 hen.2 hfr
end CCS

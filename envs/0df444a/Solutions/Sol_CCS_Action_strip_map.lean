-- Prove2me | solution 1 for CCS.Action.strip_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:37:43.487414+00:00
-- url     : https://prove2.me/submissions/fd3f2beb-5382-4504-89c4-47a49c85c75a

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_CCS_Syntax
import Theorems.Thm_CCS_Label_co_co
import Theorems.Thm_CCS_Label_strip_map
attribute [local simp] CCS.Label.co_co
attribute [local simp] CCS.Label.strip_map

set_option autoImplicit true
open CCS
open CCS.Action
variable {Name Name' : Type*}
namespace CCS.Action
theorem _root_.solution (α : Action Name) : (α.map some).strip = some α := by
  cases α <;> simp [Action.map, Action.strip]
end CCS.Action

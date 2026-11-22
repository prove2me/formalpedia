-- Prove2me | solution 1 for CCS.Label.strip_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:36:34.499588+00:00
-- url     : https://prove2.me/submissions/17ce363a-0f00-4342-9593-51e96911413a

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_CCS_Syntax

set_option autoImplicit true
open CCS
open CCS.Label
variable {Name Name' : Type*}
namespace CCS.Label
theorem _root_.solution (a : Label Name) : (a.map some).strip = some a := by cases a <;> rfl
end CCS.Label

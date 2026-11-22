-- Prove2me | solution 1 for CCS.Label.co_co
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:36:34.066266+00:00
-- url     : https://prove2.me/submissions/2f787686-b515-4adc-9b0c-34efd4b45ab1

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_CCS_Syntax

set_option autoImplicit true
open CCS
open CCS.Label
variable {Name Name' : Type*}
namespace CCS.Label
theorem _root_.solution (a : Label Name) : a.co.co = a := by cases a <;> rfl
end CCS.Label

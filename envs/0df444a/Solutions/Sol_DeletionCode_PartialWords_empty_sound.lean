-- Prove2me | solution 1 for DeletionCode.PartialWords.empty_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:04.955655+00:00
-- url     : https://prove2.me/submissions/06fc4de9-9365-47a8-aa57-ed1a50ab716f

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (p : Letters) (m : ℕ) : Sound empty p m := by
  intro j hj b hb
  simp [empty] at hb
end DeletionCode.PartialWords

-- Prove2me | solution 1 for DirLabel.rev_rev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:13:01.543703+00:00
-- url     : https://prove2.me/submissions/757abc08-796d-4e8d-b3f8-394cdff1bc93

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_LTS_Basic

set_option autoImplicit true
variable {L : Type*}
open DirLabel
namespace DirLabel
theorem _root_.solution (la : DirLabel L) : rev (rev la) = la := by cases la <;> rfl
end DirLabel

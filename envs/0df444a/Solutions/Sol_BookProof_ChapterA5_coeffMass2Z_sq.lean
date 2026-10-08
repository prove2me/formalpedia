-- Prove2me | solution 1 for BookProof.ChapterA5.coeffMass2Z_sq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T21:41:52.889313+00:00
-- url     : https://prove2.me/submissions/484c4737-caa7-4bbf-8456-0267882c657a

import Mathlib
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.ChapterA5 in open BookProof.ChapterA5 in open Matrix in open BookProof.ChapterA3 in
theorem solution : coeffMass2Z * coeffMass2Z = -1 := by
  intros
  decide

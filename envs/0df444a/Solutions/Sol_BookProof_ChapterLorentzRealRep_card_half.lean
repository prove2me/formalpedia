-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.card_half
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T16:35:02.720194+00:00
-- url     : https://prove2.me/submissions/9fec5c6b-8086-435f-a4b0-a1d8006941ba

import Mathlib
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.ChapterLorentzRealRep in open BookProof.ChapterLorentzRealRep in open Matrix in open BookProof.ChapterA3 BookProof.ChapterPinOmega in
theorem solution : (Finset.univ.image bHalf).card = 4 := by
  intros
  rfl

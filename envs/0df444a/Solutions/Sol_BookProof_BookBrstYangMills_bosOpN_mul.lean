-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bosOpN_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T15:53:08.900561+00:00
-- url     : https://prove2.me/submissions/601b064d-4b9d-4322-a42e-3874016acfb2

import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterBookBrstYangMills
import Definitions.Def_ChapterYangMillsGhostSector

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.BookBrstYangMills in open BookProof.YangMillsGhost in open BookProof.BookBrstYangMills in open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge in
theorem solution {N : ℕ} (S T : Module.End ℂ (FieldPoly N)) :
    bosOpN (S * T) = bosOpN S * bosOpN T := by
  intros
  aesop

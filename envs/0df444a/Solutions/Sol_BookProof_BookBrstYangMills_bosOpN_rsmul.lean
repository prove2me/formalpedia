-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bosOpN_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T17:49:28.521215+00:00
-- url     : https://prove2.me/submissions/1904a604-9573-4d2d-8804-b613557f6223

import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterBookBrstYangMills
import Definitions.Def_ChapterYangMillsGhostSector

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.BookBrstYangMills in open BookProof.YangMillsGhost in open BookProof.BookBrstYangMills in open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge in
theorem solution {N : ℕ} (r : ℝ) (T : Module.End ℂ (FieldPoly N)) :
    bosOpN (r • T) = r • bosOpN T := by
  intros
  aesop

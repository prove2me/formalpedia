-- Prove2me | solution 1 for BookProof.ChapterH6.generation_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T01:08:42.266988+00:00
-- url     : https://prove2.me/submissions/1f3d676b-71aa-481c-86d8-f4c65c3443cf

import Mathlib
import Definitions.Def_ChapterH6
open BookProof.ChapterH6

set_option autoImplicit false

variable {m : ℕ}

open BookProof.ChapterH6 in
theorem solution (A : Matrix (Fin m) (Fin m) ℂ) (psi0 : Fin m → ℂ) :
    generatedState A 0 psi0 = psi0 := by
  unfold generatedState
  simp [NormedSpace.exp_zero, Matrix.one_mulVec]

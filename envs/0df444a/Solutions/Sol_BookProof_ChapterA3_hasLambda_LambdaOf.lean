-- Prove2me | solution 1 for BookProof.ChapterA3.hasLambda_LambdaOf
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:53:39.651187+00:00
-- url     : https://prove2.me/submissions/6518cd5b-217e-4eaa-850b-27ea4266a85e

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix
set_option autoImplicit false
set_option maxHeartbeats 0

theorem solution (S : Matrix (Fin 4) (Fin 4) ℝ) (h : ∃ Λ, HasLambda S Λ) : HasLambda S (LambdaOf S) := by
  classical
  simpa only [LambdaOf, dif_pos h] using h.choose_spec

#print axioms solution


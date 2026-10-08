-- Prove2me | solution 1 for BookProof.ChapterA3.toC_conj
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:27:14.864594+00:00
-- url     : https://prove2.me/submissions/5403992c-0c00-4222-9fee-0f41594d24a1

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix
set_option autoImplicit false
set_option maxHeartbeats 0

theorem solution (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (toC M).map (starRingEnd ℂ) = toC M := by
  ext i j
  simp [toC]

#print axioms solution

-- Prove2me | solution 1 for BookProof.ChapterA3.toC_det
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:22:06.530265+00:00
-- url     : https://prove2.me/submissions/647747cb-bdc5-4fa8-8f1e-90abcc69c81c

import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3

open BookProof.ChapterA3
open Matrix

theorem solution (M : Matrix (Fin 4) (Fin 4) ℝ) : (toC M).det = (M.det : ℂ) := by
  rw [show toC M = Complex.ofRealHom.mapMatrix M by
    ext i j
    rfl]
  simpa using (Complex.ofRealHom.map_det M).symm

#print axioms solution

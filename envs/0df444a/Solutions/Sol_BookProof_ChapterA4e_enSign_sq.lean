-- Prove2me | solution 1 for BookProof.ChapterA4e.enSign_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:29:45.391678+00:00
-- url     : https://prove2.me/submissions/0e0152e0-8555-450f-8865-cde39be27f72

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4e

open BookProof.ChapterA4e BookProof.ChapterA3 BookProof.ChapterA5 Matrix

theorem solution : enSign * enSign = -1 := by
  have hZ : mgammaZ 0 * mgammaZ 0 = (-1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    decide
  simp only [enSign, coeffMass1Z, ← map_mul, hZ, map_neg, map_one]

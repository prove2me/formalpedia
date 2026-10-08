-- Prove2me | solution 1 for BookProof.ChapterA3.isPin_one
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:57:32.432982+00:00
-- url     : https://prove2.me/submissions/ec3190c4-745e-4573-aada-b5c80702f9dc

import Mathlib
import Definitions.Def_ChapterA3d
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3

open BookProof.ChapterA3
open Matrix

theorem solution : IsPin (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  refine ⟨by simp, by simp, ?_⟩
  refine ⟨1, ?_⟩
  intro μ
  simp [Matrix.one_apply]

#print axioms solution

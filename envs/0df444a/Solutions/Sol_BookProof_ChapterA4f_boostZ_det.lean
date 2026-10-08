-- Prove2me | solution 1 for BookProof.ChapterA4f.boostZ_det
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:08:15.097417+00:00
-- url     : https://prove2.me/submissions/9ec9387f-04b3-4b52-b53f-01a903ff7977

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.boostZ_det
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4f
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem solution {l : ℂ} (hl : l ≠ 0) : (boostZ l).det = 1 := by
  simp [boostZ, Matrix.det_fin_two, hl]

#print axioms solution


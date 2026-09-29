-- Prove2me | solution 1 for BookProof.QgOuterFock.pcoord_partOf_modeOf
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T04:59:24.771217+00:00
-- url     : https://prove2.me/submissions/a26a3bab-8d4d-4748-a8e5-ef25c49d3d97

import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.QgOuterFock

theorem solution {n : ℕ} (I : Fin (n * 84)) :
    pcoord (partOf I) (modeOf I) = I := by
  simp only [pcoord, partOf, modeOf]
  exact Equiv.apply_symm_apply finProdFinEquiv I

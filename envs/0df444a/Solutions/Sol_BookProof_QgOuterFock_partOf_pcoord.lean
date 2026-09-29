-- Prove2me | solution 1 for BookProof.QgOuterFock.partOf_pcoord
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T05:01:59.885835+00:00
-- url     : https://prove2.me/submissions/f5a01d6e-e661-4c25-86db-9937ef33109f

import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.QgOuterFock

theorem solution {n : ℕ} (p : Fin n) (i : Fin 84) : partOf (pcoord p i) = p := by
  simp [partOf, pcoord]

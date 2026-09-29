-- Prove2me | solution 1 for BookProof.QgOuterFock.modeOf_pcoord
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T04:56:18.348067+00:00
-- url     : https://prove2.me/submissions/603ef15e-e72f-4f30-9416-d96bcb3a06ca

import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.QgOuterFock

theorem solution {n : ℕ} (p : Fin n) (i : Fin 84) : modeOf (pcoord p i) = i := by
  simp [modeOf, pcoord]

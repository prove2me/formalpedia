-- Prove2me | solution 1 for BookProof.QgOuterFock.qgKappaN_pcoord
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:56:49.293171+00:00
-- url     : https://prove2.me/submissions/c55e85d9-d189-4b07-a7e2-444ef48c0586

import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.QuantumGravity3DGauge BookProof.QgOuterFock

theorem solution {n : ℕ} (p : Fin n) (i : Fin 84) :
    qgKappaN n (pcoord p i) = qgKappa i := by
  simp [qgKappaN, modeOf, pcoord]

#print axioms solution

-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.idxX_ne_idxDE
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T04:48:39.485997+00:00
-- url     : https://prove2.me/submissions/091bbcf5-fcde-4754-8315-65e7a7e6ffe4

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge

theorem solution (mu nu rho a : Fin 4) : idxX mu ≠ idxDE nu rho a := by
  intro h
  have := congrArg Fin.val h
  simp [idxX, idxDE] at this
  omega

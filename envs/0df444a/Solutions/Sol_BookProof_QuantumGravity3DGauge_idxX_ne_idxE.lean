-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.idxX_ne_idxE
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T04:48:40.834064+00:00
-- url     : https://prove2.me/submissions/861623c7-25fb-47d1-bb5a-84dfd44f8928

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge

theorem solution (mu nu a : Fin 4) : idxX mu ≠ idxE nu a := by
  intro h
  have := congrArg Fin.val h
  simp [idxX, idxE] at this
  omega

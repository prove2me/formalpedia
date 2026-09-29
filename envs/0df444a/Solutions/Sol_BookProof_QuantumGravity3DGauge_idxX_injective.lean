-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.idxX_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T04:48:43.645984+00:00
-- url     : https://prove2.me/submissions/daf1f783-9192-4e1c-8d69-9056770149d0

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge

theorem solution : Function.Injective idxX := by
  intro μ ν h
  have := congrArg Fin.val h
  simp [idxX] at this
  exact Fin.ext this

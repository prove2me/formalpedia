-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:58:22.464977+00:00
-- url     : https://prove2.me/submissions/51b1f474-f75d-45e0-8c16-11dc96c7a4c2

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgamma_map_conj
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) :
    (mgamma μ).map (starRingEnd ℂ) = mgamma μ := by

  ext i j
  simp [mgamma, RingHom.mapMatrix_apply, Matrix.map_apply]

-- Prove2me | solution 1 for BookProof.ChapterGravityIrrep.antisymPart_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:51:25.569687+00:00
-- url     : https://prove2.me/submissions/26cd287e-2106-4f9d-98a9-a26e86669c93

-- Generated from ChapterGravityIrrep.lean — solution of BookProof.ChapterGravityIrrep.antisymPart_antisymm
import Mathlib
import Definitions.Def_ChapterGravityIrrep
open BookProof.ChapterGravityIrrep




open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (antisymPart M)ᵀ = -(antisymPart M) := by

  simp [antisymPart, transpose_sub, transpose_transpose]

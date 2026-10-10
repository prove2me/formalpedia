-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.proj_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:33:23.287602+00:00
-- url     : https://prove2.me/submissions/64274cdc-4c2c-44d7-b833-5f2afa01cb7f

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.proj_smul
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (c : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    BookProof.ChapterGravityPolymomentum.proj v (c • M) = c • BookProof.ChapterGravityPolymomentum.proj v M := by

  simp [BookProof.ChapterGravityPolymomentum.proj]

-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.contract_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:27:00.145995+00:00
-- url     : https://prove2.me/submissions/56ba61ad-43ff-47ed-954e-71bd128c8e52

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.contract_smul_left
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (c : ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    contract (c • A) B = c * contract A B := by

  simp [contract]

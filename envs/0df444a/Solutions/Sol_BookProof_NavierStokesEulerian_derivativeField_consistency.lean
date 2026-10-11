-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.derivativeField_consistency
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:28.618097+00:00
-- url     : https://prove2.me/submissions/a699ccd4-fcbf-45a7-920b-4575a1607aab

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.derivativeField_consistency
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Theorems.Thm_BookProof_NavierStokesEulerian_dirDeriv_dirDeriv
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix

set_option maxHeartbeats 1000000 in
theorem solution (u : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (hu : ∀ i, ContDiff ℝ 2 (fun y => u y i)) (i j k : Fin 3) (x : Fin 3 → ℝ) :
    dirDeriv (dirDeriv (fun y => u y i) j) k x
      = dirDeriv (dirDeriv (fun y => u y i) k) j x := by

  rw [dirDeriv_dirDeriv _ (hu i), dirDeriv_dirDeriv _ (hu i)]
  exact ((hu i).contDiffAt.isSymmSndFDerivAt (by simp)) _ _

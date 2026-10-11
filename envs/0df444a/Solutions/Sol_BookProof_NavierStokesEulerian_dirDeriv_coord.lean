-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.dirDeriv_coord
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:18.183622+00:00
-- url     : https://prove2.me/submissions/8e741037-fe13-4537-9820-a4a15ac230ee

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.dirDeriv_coord
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Theorems.Thm_BookProof_NavierStokesEulerian_dirDeriv_eq
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix

set_option maxHeartbeats 1000000 in
theorem solution (k j : Fin 3) (x : Fin 3 → ℝ) :
    dirDeriv (fun y => y k) j x = if k = j then 1 else 0 := by

  have hf : HasFDerivAt (fun y : Fin 3 → ℝ => y k) (ContinuousLinearMap.proj k) x :=
    (ContinuousLinearMap.proj k : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt
  rw [dirDeriv_eq hf]
  simp [evec, Pi.single_apply]

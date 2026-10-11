-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.eulerian_divergence_constraint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:30.125032+00:00
-- url     : https://prove2.me/submissions/00983801-ffa8-4fb9-b372-4c2de80c45d9

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.eulerian_divergence_constraint
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix

set_option maxHeartbeats 1000000 in
theorem solution (u : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (h : dirDeriv (fun y => u y 2) 2 x
      = -(dirDeriv (fun y => u y 0) 0 x + dirDeriv (fun y => u y 1) 1 x)) :
    ∑ j : Fin 3, dirDeriv (fun y => u y j) j x = 0 := by

  rw [Fin.sum_univ_three, h]
  ring

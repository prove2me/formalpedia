-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.derivativeField_second
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:27.227244+00:00
-- url     : https://prove2.me/submissions/af6b95f5-bb71-4363-a17a-90abf0981314

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.derivativeField_second
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Theorems.Thm_BookProof_NavierStokesEulerian_dirDeriv_eq
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix

set_option maxHeartbeats 1000000 in
theorem solution (uD : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ)
    (uDD : Fin 3 → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ)
    (M : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] ℝ))
    (huD : ∀ i j x, HasFDerivAt (uD i j) (M i j x) x)
    (huDD : ∀ i j k x, uDD i j k x = M i j x (evec k)) (i j k : Fin 3) (x : Fin 3 → ℝ) :
    uDD i j k x = dirDeriv (uD i j) k x := by

  rw [huDD, dirDeriv_eq (huD i j x)]

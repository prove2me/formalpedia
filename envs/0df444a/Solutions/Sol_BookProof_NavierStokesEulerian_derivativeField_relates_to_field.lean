-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.derivativeField_relates_to_field
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:25.882978+00:00
-- url     : https://prove2.me/submissions/fdb4364c-536f-4a06-a7b1-92e679561852

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.derivativeField_relates_to_field
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Theorems.Thm_BookProof_NavierStokesEulerian_dirDeriv_eq
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix

set_option maxHeartbeats 1000000 in
theorem solution (u : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (uD : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ) (L : Fin 3 → (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] ℝ))
    (hu : ∀ i x, HasFDerivAt (fun y => u y i) (L i x) x)
    (huD : ∀ i j x, uD i j x = L i x (evec j)) (i j : Fin 3) (x : Fin 3 → ℝ) :
    uD i j x = dirDeriv (fun y => u y i) j x := by

  rw [huD, dirDeriv_eq (hu i x)]

-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.y_zero_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:14.286019+00:00
-- url     : https://prove2.me/submissions/52abd252-57f3-4383-9c08-abb280a58b93

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.y_zero_of_commute
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (Y : Fin 3 → E →ₗ[ℂ] E) (T : E →ₗ[ℂ] E)
    (hT : ∀ j, Y j ∘ₗ T = T ∘ₗ Y j) (v : E) (hv : ∀ j, Y j v = 0) (j : Fin 3) :
    Y j (T v) = 0 := by

  have := congrArg (fun L : E →ₗ[ℂ] E => L v) (hT j)
  simpa [hv j] using this

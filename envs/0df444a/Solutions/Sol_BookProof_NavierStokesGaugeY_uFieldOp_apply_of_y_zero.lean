-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.uFieldOp_apply_of_y_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:13.078924+00:00
-- url     : https://prove2.me/submissions/17bf73dc-af34-4b30-ab34-9d6f9db583f4

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.uFieldOp_apply_of_y_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Theorems.Thm_BookProof_NavierStokesFlow_field_evaluates_to_value
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E)
    (Y : Fin 3 → E →ₗ[ℂ] E) (v : E) (hv : ∀ j, Y j v = 0) (i : Fin 3) :
    uFieldOp u uD Y i v = u i v := field_evaluates_to_value (u i) (uD i) Y 0 v (by simpa using hv)

-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.advectionOp_apply_of_y_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:15.519517+00:00
-- url     : https://prove2.me/submissions/29d85ea6-d9ab-4713-b3b2-2801b2cb7307

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.advectionOp_apply_of_y_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Theorems.Thm_BookProof_NavierStokesGaugeY_uFieldOp_apply_of_y_zero
import Theorems.Thm_BookProof_NavierStokesGaugeY_y_zero_of_commute
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (nu : ℂ) (u : Fin 3 → E →ₗ[ℂ] E)
    (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E) (uL : Fin 3 → E →ₗ[ℂ] E) (Y : Fin 3 → E →ₗ[ℂ] E)
    (hcomm : ∀ i j k, Y k ∘ₗ uD i j = uD i j ∘ₗ Y k) (v : E) (hv : ∀ j, Y j v = 0)
    (i : Fin 3) :
    advectionOp nu u uD uL Y i v = advectionPoint nu u uD uL i v := by

  simp only [advectionOp, advectionPoint, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact uFieldOp_apply_of_y_zero u uD Y (uD i j v)
    (fun k => y_zero_of_commute Y (uD i j) (fun k => hcomm i j k) v hv k) j

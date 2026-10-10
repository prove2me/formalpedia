-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.hamiltonianOp_apply_of_y_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:16.900494+00:00
-- url     : https://prove2.me/submissions/605f9178-19c1-43ff-9fdb-20ab519f1a57

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.hamiltonianOp_apply_of_y_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Theorems.Thm_BookProof_NavierStokesGaugeY_y_zero_of_commute
import Theorems.Thm_BookProof_NavierStokesGaugeY_advectionOp_apply_of_y_zero
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (nu : ℂ) (mom : Fin 3 → E →ₗ[ℂ] E)
    (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E) (uL : Fin 3 → E →ₗ[ℂ] E)
    (Y : Fin 3 → E →ₗ[ℂ] E) (hcomm : ∀ i j k, Y k ∘ₗ uD i j = uD i j ∘ₗ Y k)
    (hmom : ∀ i k, Y k ∘ₗ mom i = mom i ∘ₗ Y k) (v : E) (hv : ∀ j, Y j v = 0) :
    hamiltonianOp nu mom u uD uL Y v = hamiltonianPoint nu mom u uD uL v := by

  simp only [hamiltonianOp, hamiltonianPoint, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : advectionOp nu u uD uL Y i v = advectionPoint nu u uD uL i v :=
    advectionOp_apply_of_y_zero nu u uD uL Y hcomm v hv i
  have h2 : advectionOp nu u uD uL Y i (mom i v) = advectionPoint nu u uD uL i (mom i v) :=
    advectionOp_apply_of_y_zero nu u uD uL Y hcomm (mom i v)
      (fun k => y_zero_of_commute Y (mom i) (fun k => hmom i k) v hv k) i
  rw [h1, h2]

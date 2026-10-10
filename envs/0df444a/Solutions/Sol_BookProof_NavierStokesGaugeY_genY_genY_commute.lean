-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genY_genY_commute
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:10.438994+00:00
-- url     : https://prove2.me/submissions/9bcb02db-eaa4-4b7b-b990-2dcd8aecdf49

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genY_genY_commute
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Theorems.Thm_BookProof_NavierStokesGaugeY_pderiv_swap
import Theorems.Thm_BookProof_NavierStokesGaugeY_genY_genY_expand
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin 3) : ⁅genY j, genY k⁆ = 0 := by

  refine LinearMap.ext fun p => ?_
  have hsum : ∑ i : Fin 3, ∑ m : Fin 3,
        X (NSVar.uD i j) * X (NSVar.uD m k) * pderiv (NSVar.u i) (pderiv (NSVar.u m) p)
      = ∑ i : Fin 3, ∑ m : Fin 3,
        X (NSVar.uD i k) * X (NSVar.uD m j) * pderiv (NSVar.u i) (pderiv (NSVar.u m) p) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    rw [pderiv_swap (NSVar.u m) (NSVar.u i)]
    ring
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply,
    genY_genY_expand, pderiv_swap (NSVar.y j) (NSVar.y k), hsum]
  ring

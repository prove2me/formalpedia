-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genY_genY_expand
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:09.18316+00:00
-- url     : https://prove2.me/submissions/61ff4496-8142-41c6-9bc9-9b034e20244a

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genY_genY_expand
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Theorems.Thm_BookProof_NavierStokesGaugeY_pderiv_swap
import Theorems.Thm_BookProof_NavierStokesGaugeY_pderiv_u_mul_uD
import Theorems.Thm_BookProof_NavierStokesGaugeY_pderiv_y_mul_uD
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow


private theorem genY_apply (j : Fin 3) (p : NSAlg) :
    genY j p = pderiv (NSVar.y j) p - ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p := by
  simp [genY]

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin 3) (p : NSAlg) :
    genY j (genY k p) =
      pderiv (NSVar.y j) (pderiv (NSVar.y k) p)
      - ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.y k) (pderiv (NSVar.u i) p)
      - ∑ i : Fin 3, X (NSVar.uD i k) * pderiv (NSVar.y j) (pderiv (NSVar.u i) p)
      + ∑ i : Fin 3, ∑ m : Fin 3,
          X (NSVar.uD i j) * X (NSVar.uD m k) * pderiv (NSVar.u i) (pderiv (NSVar.u m) p) := by

  simp only [genY_apply, map_sub, map_sum, pderiv_u_mul_uD, pderiv_y_mul_uD,
    Finset.sum_sub_distrib, pderiv_swap (NSVar.u _) (NSVar.y _)]
  rw [Finset.sum_comm]
  ring_nf

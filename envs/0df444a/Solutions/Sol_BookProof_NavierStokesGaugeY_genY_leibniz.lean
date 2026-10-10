-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genY_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:05:47.571175+00:00
-- url     : https://prove2.me/submissions/900d9329-9fd5-455d-a3f7-40cfca5bd4c6

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genY_leibniz
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow


private theorem genY_apply (j : Fin 3) (p : NSAlg) :
    genY j p = pderiv (NSVar.y j) p - ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p := by
  simp [genY]

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) (p q : NSAlg) :
    genY j (p * q) = genY j p * q + p * genY j q := by

  have key : ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) (p * q)
      = (∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p) * q
        + p * ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) q := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pderiv_mul]; ring
  rw [genY_apply, genY_apply, genY_apply, key, pderiv_mul]
  ring

-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genY_ccr_y
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:06:42.820933+00:00
-- url     : https://prove2.me/submissions/8bfd3d6f-aea7-4cd9-a1de-67abc43aa02e

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genY_ccr_y
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow


private theorem genY_apply (j : Fin 3) (p : NSAlg) :
    genY j p = pderiv (NSVar.y j) p - ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p := by
  simp [genY]

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin 3) (p : NSAlg) :
    genY j (X (NSVar.y k) * p) - X (NSVar.y k) * genY j p = if j = k then p else 0 := by

  have hsum : ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) (X (NSVar.y k) * p)
      = X (NSVar.y k) * ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pderiv_mul, pderiv_X_of_ne (by simp)]; ring
  rw [genY_apply, genY_apply, hsum, pderiv_mul, pderiv_X, Pi.single_apply]
  simp only [NSVar.y.injEq]
  by_cases h : j = k
  · subst h; simp; ring
  · rw [if_neg (fun hh : k = j => h hh.symm), if_neg h]; ring

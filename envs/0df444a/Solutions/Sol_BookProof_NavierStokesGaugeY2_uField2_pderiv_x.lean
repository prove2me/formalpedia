-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.uField2_pderiv_x
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:26.78557+00:00
-- url     : https://prove2.me/submissions/be38a293-4cb4-4e95-a36e-81cdbdb980ee

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.uField2_pderiv_x
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) : pderiv (NSVar.x j) (uField2 i) = 0 := by

  have h1 : pderiv (NSVar.x j) (X (NSVar.u i) : NSAlg) = 0 := by simp [pderiv_X]
  have h2 : ∀ k : Fin 3, pderiv (NSVar.x j) (X (NSVar.uD i k) * X (NSVar.y k) : NSAlg) = 0 := by
    intro k; rw [pderiv_mul]; simp [pderiv_X]
  have h3 : ∀ k : Fin 3,
      pderiv (NSVar.x j) (X (NSVar.uL i) * (X (NSVar.y k) * X (NSVar.y k)) : NSAlg) = 0 := by
    intro k; rw [pderiv_mul, pderiv_mul]; simp [pderiv_X]
  rw [uField2, map_add, map_add, h1, map_sum, MvPolynomial.pderiv_C_mul, map_sum,
    Finset.sum_eq_zero (fun k _ => h2 k), Finset.sum_eq_zero (fun k _ => h3 k)]
  simp

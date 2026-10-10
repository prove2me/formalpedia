-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.uField2_pderiv_u
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:24.37789+00:00
-- url     : https://prove2.me/submissions/a970c494-96c4-4d36-84b1-907f40fdeb49

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.uField2_pderiv_u
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution (m i : Fin 3) :
    pderiv (NSVar.u m) (uField2 i) = if m = i then 1 else 0 := by

  have h2 : ∀ k : Fin 3, pderiv (NSVar.u m) (X (NSVar.uD i k) * X (NSVar.y k) : NSAlg) = 0 := by
    intro k; rw [pderiv_mul]; simp [pderiv_X]
  have h3 : ∀ k : Fin 3,
      pderiv (NSVar.u m) (X (NSVar.uL i) * (X (NSVar.y k) * X (NSVar.y k)) : NSAlg) = 0 := by
    intro k; rw [pderiv_mul, pderiv_mul]; simp [pderiv_X]
  rw [uField2, map_add, map_add, map_sum, MvPolynomial.pderiv_C_mul, map_sum,
    Finset.sum_eq_zero (fun k _ => h2 k), Finset.sum_eq_zero (fun k _ => h3 k)]
  simp [pderiv_X, Pi.single_apply, @eq_comm _ i m]

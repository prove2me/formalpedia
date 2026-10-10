-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genY2_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:08:33.456707+00:00
-- url     : https://prove2.me/submissions/78849d9b-5b5c-41a0-86f5-eeb328e77079

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.genY2_leibniz
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY


private theorem genY2_apply (j : Fin 3) (p : NSAlg) :
    genY2 j p = pderiv (NSVar.y j) p
      - (∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p)
      - ∑ i : Fin 3, X (NSVar.uL i) * pderiv (NSVar.uD i j) p := by
  simp [genY2]

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) (p q : NSAlg) :
    genY2 j (p * q) = genY2 j p * q + p * genY2 j q := by

  have key : ∀ (f : Fin 3 → NSVar) (c : Fin 3 → NSAlg),
      ∑ i : Fin 3, c i * pderiv (f i) (p * q)
        = (∑ i : Fin 3, c i * pderiv (f i) p) * q + p * ∑ i : Fin 3, c i * pderiv (f i) q := by
    intro f c
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pderiv_mul]; ring
  rw [genY2_apply, genY2_apply, genY2_apply, key (fun i => NSVar.u i) _,
    key (fun i => NSVar.uD i j) _, pderiv_mul]
  ring

-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.end_ext_of_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:17.999699+00:00
-- url     : https://prove2.me/submissions/ce76dd8b-2136-4a70-a20e-2496b2efe092

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.end_ext_of_leibniz
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution (D : Module.End ℂ NSAlg)
    (hL : ∀ p q, D (p * q) = D p * q + p * D q)
    (hC : ∀ c : ℂ, D (C c) = 0) (hX : ∀ v, D (X v) = 0) : D = 0 := by

  refine LinearMap.ext fun p => ?_
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hC c
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p v hp =>
      simp only [LinearMap.zero_apply] at hp ⊢
      rw [hL, hp, hX]; ring

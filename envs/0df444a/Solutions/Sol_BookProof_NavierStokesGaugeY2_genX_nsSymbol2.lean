-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genX_nsSymbol2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:37.123699+00:00
-- url     : https://prove2.me/submissions/aeb116b6-1c98-473e-9b52-c4df6eca7651

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.genX_nsSymbol2
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NavierStokesGaugeY2_genX_uField2
import Theorems.Thm_BookProof_NavierStokesGaugeY_genX_leibniz
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY


@[simp] private theorem genX_apply (j : Fin 3) (p : NSAlg) : genX j p = pderiv (NSVar.x j) p := rfl

set_option maxHeartbeats 1000000 in
theorem solution (nu : ℂ) (i j : Fin 3) : genX j (nsSymbol2 nu i) = 0 := by

  have huD : ∀ k : Fin 3, genX j (uDField i k) = 0 := by
    intro k
    simp [uDField, genX_apply, pderiv_X]
  have huL : genX j (X (NSVar.uL i)) = 0 := by simp
  have hC : genX j (C nu) = 0 := by simp
  simp only [nsSymbol2, map_sub, map_sum, genX_leibniz, genX_uField2, huD, huL, hC,
    zero_mul, mul_zero, add_zero, Finset.sum_const_zero, sub_self]

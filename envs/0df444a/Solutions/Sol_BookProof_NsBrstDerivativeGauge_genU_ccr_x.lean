-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.genU_ccr_x
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T03:43:50.46366+00:00
-- url     : https://prove2.me/submissions/426e91b9-45e1-4db3-b6fa-0b78b0633c6d

import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Definitions.Def_ChapterNavierStokesGaugeY2

open MvPolynomial BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2 BookProof.NsBrstDerivativeGauge in
theorem solution (i k : Fin 3) (p : NSAlg) :
    genU i (X (NSVar.x k) * p) - X (NSVar.x k) * genU i p = 0 := by
  simp [genU_apply, Derivation.leibniz, pderiv_X, Pi.single_apply]

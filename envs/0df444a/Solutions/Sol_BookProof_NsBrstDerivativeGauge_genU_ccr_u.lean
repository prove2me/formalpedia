-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.genU_ccr_u
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:43:52.798471+00:00
-- url     : https://prove2.me/submissions/d16a45e2-4f3a-4ecf-bc84-28d5e26f6b4c

import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Definitions.Def_ChapterNavierStokesGaugeY2

open MvPolynomial BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2 BookProof.NsBrstDerivativeGauge in
theorem solution (i k : Fin 3) (p : NSAlg) :
    genU i (X (NSVar.u k) * p) - X (NSVar.u k) * genU i p = if i = k then p else 0 := by
  simp only [genU_apply, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul]
  by_cases h : i = k
  · subst h; simp
  · simp [h, Ne.symm h]

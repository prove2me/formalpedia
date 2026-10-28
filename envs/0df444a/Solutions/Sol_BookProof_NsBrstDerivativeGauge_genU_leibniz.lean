-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.genU_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T03:43:54.022996+00:00
-- url     : https://prove2.me/submissions/06038811-6d1d-4bb7-bca2-3f6da672f116

import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Definitions.Def_ChapterNavierStokesGaugeY2

open MvPolynomial BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2 BookProof.NsBrstDerivativeGauge in
theorem solution (i : Fin 3) (p q : NSAlg) :
    genU i (p * q) = genU i p * q + p * genU i q := by
  simp only [genU_apply, Derivation.leibniz, smul_eq_mul]
  ring

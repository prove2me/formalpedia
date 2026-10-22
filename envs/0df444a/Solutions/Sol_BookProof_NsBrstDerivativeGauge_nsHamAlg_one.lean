-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.nsHamAlg_one
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:43:57.21743+00:00
-- url     : https://prove2.me/submissions/fbef4daf-af08-4f91-b786-010e7e9eec8c

import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Definitions.Def_ChapterNavierStokesGaugeY2

open MvPolynomial BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2 BookProof.NsBrstDerivativeGauge in
theorem solution (nu : ℂ) : nsHamAlg nu 1 = ∑ i : Fin 3, X (NSVar.uD i i) := by
  simp [nsHamAlg, genU_apply, BookProof.NsBrstDerivativeGauge.mulOp, nsSymbol, uField, Derivation.leibniz, pderiv_X, Pi.single_apply, map_sum]

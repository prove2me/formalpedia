-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.pderiv_u_mul_uL
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:28:36.565773+00:00
-- url     : https://prove2.me/submissions/7159bd84-4714-4212-8df3-db3a73750876

-- Generated from ChapterNsBrstDerivativeGauge.lean — solution of BookProof.NsBrstDerivativeGauge.pderiv_u_mul_uL
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NsBrstDerivativeGauge




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2
open BookProof.NavierStokesGaugeY

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (m i : Fin 3) (q : NSAlg) :
    pderiv (NSVar.u m) (X (NSVar.uL i) * q) = X (NSVar.uL i) * pderiv (NSVar.u m) q := by

  rw [pderiv_mul, pderiv_X_of_ne (by simp)]; ring

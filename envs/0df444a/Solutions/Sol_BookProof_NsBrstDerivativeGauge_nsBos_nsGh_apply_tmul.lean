-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.nsBos_nsGh_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:30:42.992481+00:00
-- url     : https://prove2.me/submissions/b2cacc91-8fda-444b-b160-4b54a612d19b

-- Generated from ChapterNsBrstDerivativeGauge.lean — solution of BookProof.NsBrstDerivativeGauge.nsBos_nsGh_apply_tmul
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
theorem solution (S : Module.End ℂ NSAlg) (T : Module.End ℂ nsGhostSpace)
    (p : NSAlg) (w : nsGhostSpace) :
    (nsBos S * nsGh T) (p ⊗ₜ[ℂ] w) = S p ⊗ₜ[ℂ] T w := by

  simp [nsBos, nsGh, Module.End.mul_apply]

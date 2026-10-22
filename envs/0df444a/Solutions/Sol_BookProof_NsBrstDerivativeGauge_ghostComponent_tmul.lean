-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.ghostComponent_tmul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:32:16.228727+00:00
-- url     : https://prove2.me/submissions/c4283b56-d675-420d-a7fe-537156f87ef5

-- Generated from ChapterNsBrstDerivativeGauge.lean — solution of BookProof.NsBrstDerivativeGauge.ghostComponent_tmul
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
theorem solution (p : NSAlg) (w : nsGhostSpace) :
    ghostComponent (p ⊗ₜ[ℂ] w) = (MvPolynomial.aeval (fun _ => (0 : ℂ)) p) • w := by

  simp [ghostComponent]

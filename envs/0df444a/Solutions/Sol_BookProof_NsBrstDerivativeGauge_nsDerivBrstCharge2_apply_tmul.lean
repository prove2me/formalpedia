-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:32:14.640123+00:00
-- url     : https://prove2.me/submissions/09533c8e-7382-42c0-a10a-1cc9a181dcfb

-- Generated from ChapterNsBrstDerivativeGauge.lean — solution of BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_apply_tmul
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Theorems.Thm_BookProof_NsBrstDerivativeGauge_glin_bos_apply_tmul
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesGaugeY2
open BookProof.NsBrstDerivativeGauge




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (p : NSAlg) (w : nsGhostSpace) :
    nsDerivBrstCharge2 (p ⊗ₜ[ℂ] w) = ∑ j : Fin 3, genY2 j p ⊗ₜ[ℂ] nsGhostCre j w := glin_bos_apply_tmul genY2 p w

-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.glin_bos_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:30:55.787704+00:00
-- url     : https://prove2.me/submissions/156932bf-0e0b-4e04-a091-b485337ec9c0

-- Generated from ChapterNsBrstDerivativeGauge.lean — solution of BookProof.NsBrstDerivativeGauge.glin_bos_apply_tmul
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Theorems.Thm_BookProof_NsBrstDerivativeGauge_nsBos_nsGh_apply_tmul
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
theorem solution (G : Fin 3 → Module.End ℂ NSAlg) (p : NSAlg) (w : nsGhostSpace) :
    glin (fun j => nsBos (G j)) nsChi (p ⊗ₜ[ℂ] w)
      = ∑ j : Fin 3, G j p ⊗ₜ[ℂ] nsGhostCre j w := by

  rw [glin, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => nsBos_nsGh_apply_tmul (G j) (nsGhostCre j) p w

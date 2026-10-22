-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.nsGaugeConstraint_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:30:24.927243+00:00
-- url     : https://prove2.me/submissions/c58d6c51-93e5-4e45-9163-f445e7abc16a

-- Generated from ChapterNsBrstDerivativeGauge.lean — solution of BookProof.NsBrstDerivativeGauge.nsGaugeConstraint_comm
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Theorems.Thm_BookProof_NavierStokesGaugeY_genY_genY_commute
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
theorem solution (j k : Fin 3) :
    nsGaugeConstraint j * nsGaugeConstraint k = nsGaugeConstraint k * nsGaugeConstraint j := by

  have h := genY_genY_commute j k
  rw [Ring.lie_def, sub_eq_zero] at h
  rw [nsGaugeConstraint, nsGaugeConstraint, ← nsBos_mul, ← nsBos_mul, h]

-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.nsGaugeConstraint2_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:30:26.237216+00:00
-- url     : https://prove2.me/submissions/2c14ecf1-bd08-47c3-a775-12a654f4e897

-- Generated from ChapterNsBrstDerivativeGauge.lean — solution of BookProof.NsBrstDerivativeGauge.nsGaugeConstraint2_comm
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Theorems.Thm_BookProof_NavierStokesGaugeY2_genY2_genY2_commute
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
theorem solution (j k : Fin 3) :
    nsGaugeConstraint2 j * nsGaugeConstraint2 k
      = nsGaugeConstraint2 k * nsGaugeConstraint2 j := by

  have h := genY2_genY2_commute j k
  rw [Ring.lie_def, sub_eq_zero] at h
  rw [nsGaugeConstraint2, nsGaugeConstraint2, ← nsBos_mul, ← nsBos_mul, h]

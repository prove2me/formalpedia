-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_dag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:11.41226+00:00
-- url     : https://prove2.me/submissions/970f56e7-5137-4d2f-864c-450607e1a1cc

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_apply
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_tau_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution {l : Fin r} {Z : Mx k r} (hZ : Pat k r l Z) : Pat k r l (dag k r Z) := by
  intro i j h
  rw [dag_apply] at h
  have hZ' : Z (WeylGroupFacts.tau k r j) (WeylGroupFacts.tau k r i) ≠ 0 := by
    intro h0
    apply h
    rw [h0, star_zero, mul_zero, zero_mul]
  have hp := hZ _ _ hZ'
  rw [tau_val, tau_val] at hp
  have := l.isLt
  have := i.isLt
  have := j.isLt
  split_ifs at hp <;> omega
end Formalism.FourierDecayAlt.Q.QRR

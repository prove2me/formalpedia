-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.skew_hpart1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:20:37.073016+00:00
-- url     : https://prove2.me/submissions/256f9fd1-5b81-4917-b470-885f79428804

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_sub
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_dag
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_star_half

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
theorem _root_.solution (Z : Mx k r) : dag k r (hpart1 (Hpk k r) Z) = -hpart1 (Hpk k r) Z := by
  have e : hpart1 (Hpk k r) Z = (1 / 2 : ℂ) • (Z - dag k r Z) := rfl
  rw [e, dag_smul, dag_sub, dag_dag, star_half, ← smul_neg, neg_sub]
end Formalism.FourierDecayAlt.Q.QRR

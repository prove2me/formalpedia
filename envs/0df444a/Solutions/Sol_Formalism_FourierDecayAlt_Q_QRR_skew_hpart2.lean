-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.skew_hpart2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:15:52.251548+00:00
-- url     : https://prove2.me/submissions/3844664f-4b49-440e-a5d2-18da85f4b717

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_dag
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_star_inv2I

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
theorem _root_.solution (Z : Mx k r) : dag k r (hpart2 (Hpk k r) Z) = -hpart2 (Hpk k r) Z := by
  have e : hpart2 (Hpk k r) Z = (1 / (2 * Complex.I) : ℂ) • (Z + dag k r Z) := rfl
  rw [e, dag_smul, dag_add, dag_dag, star_inv2I, neg_smul, add_comm (dag k r Z) Z]
end Formalism.FourierDecayAlt.Q.QRR

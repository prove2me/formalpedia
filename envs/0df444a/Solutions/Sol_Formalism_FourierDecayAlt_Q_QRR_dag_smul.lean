-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.dag_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:53:11.64408+00:00
-- url     : https://prove2.me/submissions/b340b428-cfd6-41fe-bb5d-da170b1827da

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero

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
theorem _root_.solution (c : ℂ) (A : Mx k r) : dag k r (c • A) = star c • dag k r A := by
  unfold dag
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
end Formalism.FourierDecayAlt.Q.QRR

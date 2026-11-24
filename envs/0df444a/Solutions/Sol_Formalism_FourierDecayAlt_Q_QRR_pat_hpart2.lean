-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_hpart2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:50.645618+00:00
-- url     : https://prove2.me/submissions/a3217f1c-71b7-4a54-b41f-d4d1504362f3

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_dag
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_smul

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
theorem _root_.solution {l : Fin r} {Z : Mx k r} (hZ : Pat k r l Z) : Pat k r l (hpart2 (Hpk k r) Z) :=
  pat_smul (1 / (2 * Complex.I) : ℂ) (pat_add hZ (pat_dag hZ))
end Formalism.FourierDecayAlt.Q.QRR

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_hpart1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:29:13.208882+00:00
-- url     : https://prove2.me/submissions/a76b26f9-689f-4b41-b5d4-f9f9d72532b3

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_dag
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_sub

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
theorem _root_.solution {l : Fin r} {Z : Mx k r} (hZ : Pat k r l Z) : Pat k r l (hpart1 (Hpk k r) Z) :=
  pat_smul (1 / 2 : ℂ) (pat_sub hZ (pat_dag hZ))
end Formalism.FourierDecayAlt.Q.QRR

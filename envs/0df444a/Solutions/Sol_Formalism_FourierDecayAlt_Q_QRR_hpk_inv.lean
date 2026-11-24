-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.hpk_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:47:24.321828+00:00
-- url     : https://prove2.me/submissions/b5cc0a26-b04f-4352-ba69-a06bf420c75d

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_QuantumDeterminants_hermitian_pos_facts_hold


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
theorem _root_.solution : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (hermitian_pos_facts_hold k r).2.1
end Formalism.FourierDecayAlt.Q.QRR

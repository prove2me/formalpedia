-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.eI_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:47:39.50526+00:00
-- url     : https://prove2.me/submissions/742a4d53-e773-42bb-b8c1-28dca0550aee

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution (a : Fin r) : (eI k r a).val = a.val := rfl
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule

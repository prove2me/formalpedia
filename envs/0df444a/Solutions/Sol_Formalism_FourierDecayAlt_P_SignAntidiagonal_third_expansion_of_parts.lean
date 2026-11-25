-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.third_expansion_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:46.344445+00:00
-- url     : https://prove2.me/submissions/f33fcefd-2696-40ac-9690-329cf8d54970

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_column_indicator_expansion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution : ExpansionThirdCaseFromComponents := by
  unfold ExpansionThirdCaseFromComponents
  intros
  exact column_indicator_expansion
end Formalism.FourierDecayAlt.P.SignAntidiagonal

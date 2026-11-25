-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.invRowFunctionalLast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:54:24.371595+00:00
-- url     : https://prove2.me/submissions/870049b8-fa5b-4126-b088-9ea5512aac21

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x1_lamN_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.LamLast := by
  intro K _ R n Z
  exact lamN_last R Z n rfl
end Formalism.FourierDecayAlt.P

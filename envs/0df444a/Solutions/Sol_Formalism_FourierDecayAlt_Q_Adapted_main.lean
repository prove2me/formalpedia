-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.Adapted.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:00.926974+00:00
-- url     : https://prove2.me/submissions/c29a1255-f089-468a-b4a3-e3d9bb658138

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_chatAdapted_of
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_chat2Adapted_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.Adapted
open Formalism.REAL
namespace Formalism.FourierDecayAlt.Q.Adapted
theorem _root_.solution : ContractionsCovariant → ChatAdapted ∧ Chat2Adapted := fun h => ⟨chatAdapted_of h, chat2Adapted_of h⟩
end Formalism.FourierDecayAlt.Q.Adapted

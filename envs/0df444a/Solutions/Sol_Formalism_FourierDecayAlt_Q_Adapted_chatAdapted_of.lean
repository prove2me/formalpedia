-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.Adapted.chatAdapted_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:09.73247+00:00
-- url     : https://prove2.me/submissions/f4d036e0-aa6e-4677-b258-fbabd35acfa9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_mulVec_col
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_chatA_single

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
theorem _root_.solution (hcov : ContractionsCovariant) : ChatAdapted := by
  intro A _ _ n E P Q hE hQP hPQ u β hβ
  have h := (hcov A (n + 1) E P Q hE hQP hPQ u (fun p => P p (Fin.last n)) 0 β 0).2.1
  rw [← h, mulVec_col P Q hQP (Fin.last n)]
  exact chatA_single _ u (Fin.last n) (β ᵥ* P) hβ
end Formalism.FourierDecayAlt.Q.Adapted

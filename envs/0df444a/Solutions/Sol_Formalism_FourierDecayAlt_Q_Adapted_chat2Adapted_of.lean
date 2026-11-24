-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.Adapted.chat2Adapted_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:49:50.883024+00:00
-- url     : https://prove2.me/submissions/404edddd-b6c1-4b8d-bbef-deb685089b46

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_mulVec_col
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_second_capelli_minor_standard_basis

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
theorem _root_.solution (hcov : ContractionsCovariant) : Chat2Adapted := by
  intro A _ _ n E P Q hE hQP hPQ u β β' hβ
  have h := (hcov A (n + 2) E P Q hE hQP hPQ u (fun p => P p 0) (fun p => P p 1) β β').2.2
  rw [← h, mulVec_col P Q hQP 0, mulVec_col P Q hQP 1]
  exact second_capelli_minor_standard_basis _ u (β ᵥ* P) (β' ᵥ* P) hβ
end Formalism.FourierDecayAlt.Q.Adapted

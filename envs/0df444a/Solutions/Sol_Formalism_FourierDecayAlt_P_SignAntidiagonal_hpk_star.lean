-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.hpk_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:53:50.716473+00:00
-- url     : https://prove2.me/submissions/24320517-04c3-487c-962b-0449acd2d407

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictMonoSnoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hpk_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hpk_symm

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
theorem _root_.solution (k r : ℕ) (p q : Fin (2 * r + k + 1)) : star (Hpk k r p q) = Hpk k r q p := by
  rw [hpk_real, hpk_symm]
end Formalism.FourierDecayAlt.P.SignAntidiagonal

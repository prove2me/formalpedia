-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.prod_ep_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:23:58.689984+00:00
-- url     : https://prove2.me/submissions/26783fc7-a6c2-4c43-ad06-cbe98cd9044e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_ep_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution {m : ℕ} (c : Fin m → Fin (2 * r + k + 1)) : (∏ l, ep (c l)) * (∏ l, ep (c l)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun l _ => ep_sq _
end Formalism.FourierDecayAlt.P.PBG

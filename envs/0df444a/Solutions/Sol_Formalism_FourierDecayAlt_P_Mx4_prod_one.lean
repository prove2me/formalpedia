-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.prod_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:27.803733+00:00
-- url     : https://prove2.me/submissions/17be3c94-7485-497a-ab27-92b252dcbcf9

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_fun
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_sR_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_sR_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (P : Par) (l j : ℕ) (π π1 π2 : Ty P) (h1 : Up P l π π1) (h2 : Up P j π1 π2) :
    (sR P j * sR P l) π2 π = Real.sqrt (Nrm P j π1) * Real.sqrt (Nrm P l π) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single π1 (fun b _ hb => by
    rw [sR_neg (l := l) (π := π) (π' := b) (fun hb' => hb (up_fun P l π b π1 hb' h1)), mul_zero])
    (fun h => absurd (Finset.mem_univ _) h), sR_pos h1, sR_pos h2]
end Formalism.FourierDecayAlt.P.Mx4

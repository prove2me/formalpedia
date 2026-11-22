-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.ioR_sR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:28.647973+00:00
-- url     : https://prove2.me/submissions/85be7421-4724-4375-aa2a-5280fa1a4c8c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_apply

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
theorem _root_.solution (P : Par) (l : ℕ) : ioR P (sR P l) = SS P l := by
  ext π' π
  rw [ioR_apply]
  simp only [sR, SS, Matrix.of_apply]
  split_ifs
  · rfl
  · simp
end Formalism.FourierDecayAlt.P.Mx4

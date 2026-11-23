-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.ioR_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:27.884342+00:00
-- url     : https://prove2.me/submissions/fa5dd689-b895-4cba-bae0-7c205aab472a

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
theorem _root_.solution (P : Par) (M : Matrix (Ty P) (Ty P) ℝ) : ioR P M.transpose = star (ioR P M) := by
  ext a b
  rw [Matrix.star_apply, ioR_apply, ioR_apply, Matrix.transpose_apply, ← algebraMap_star_comm]
  simp
end Formalism.FourierDecayAlt.P.Mx4

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.ioR_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:27.438739+00:00
-- url     : https://prove2.me/submissions/8d680877-7fa2-4cec-8f8d-bd75b5b2ffdc

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_kap_eq

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
theorem _root_.solution (P : Par) (f : Ty P → ℝ) : ioR P (Matrix.diagonal f) = kap P fun π => ((f π : ℝ) : ℂ) := by
  rw [kap_eq]
  ext a b
  rw [ioR_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h]
end Formalism.FourierDecayAlt.P.Mx4

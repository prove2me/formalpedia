-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.eci
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:09.084446+00:00
-- url     : https://prove2.me/submissions/f35f2524-ca30-41a9-bf99-04e4997cf50d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_euler_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ec

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
theorem _root_.solution (v w : Var r) : euler v (coord w)⁻¹ = if v = w then -(coord w)⁻¹ else 0 := by
  rw [euler_inv _ _ (coord_ne r w), ec]
  split_ifs
  · field_simp [coord_ne r w]
  · simp
end Formalism.FourierDecayAlt.P.Mx4

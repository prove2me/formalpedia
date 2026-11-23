-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.key_zb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:10.802435+00:00
-- url     : https://prove2.me/submissions/afe24633-574e-4ee9-b12e-12e291c0ccec

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_eulerLeibniz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_euler_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_euler_gg_zb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_gg_ne

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
theorem _root_.solution (TT : ℝ) : (coord vzb)⁻¹ * euler vzb (coord vzb * (gg TT)⁻¹ : Fn r) =
    -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹)) := by
  have hg : (coord vz * coord vzb : Fn r) = gg TT + algebraMap ℂ (Fn r) (TT : ℂ) := by unfold gg; ring
  have h1 := gg_ne (r := r) TT
  have h2 := coord_ne r vzb
  rw [eulerLeibniz, ec, if_pos rfl, euler_inv _ _ h1, euler_gg_zb, hg]
  field_simp
  ring
end Formalism.FourierDecayAlt.P.Mx4

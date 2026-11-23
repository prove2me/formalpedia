-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.euler_zeta_gamma_inv_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:10.554534+00:00
-- url     : https://prove2.me/submissions/da6f4c86-7530-4e51-9ec7-8cb6d8d98cbb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_eulerLeibniz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_euler_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_euler_GG_z
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
theorem _root_.solution (TT : ℝ) : (coord vz)⁻¹ * euler vz (coord vz * (gg TT)⁻¹ : Fn r) =
    -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹)) := by
  have hg : (coord vz * coord vzb : Fn r) = gg TT + algebraMap ℂ (Fn r) (TT : ℂ) := by unfold gg; ring
  have h1 := gg_ne (r := r) TT
  have h2 := coord_ne r vz
  rw [eulerLeibniz, ec, if_pos rfl, euler_inv _ _ h1, euler_GG_z, hg]
  field_simp
  ring
end Formalism.FourierDecayAlt.P.Mx4

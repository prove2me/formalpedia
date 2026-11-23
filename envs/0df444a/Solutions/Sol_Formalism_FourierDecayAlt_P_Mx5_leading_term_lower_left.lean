-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.leading_term_lower_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:16.901833+00:00
-- url     : https://prove2.me/submissions/1ad1f181-6675-494a-9066-7b66fd6828cb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_coeff_S21
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_coeff_l0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_gg_zb_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_coeff_t22

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (hk : 1 ≤ P.k) : Lead P.k (-zbA P) (t21 P) := by
  have h1 := ((leading_coeff_t22 P).mul (leading_coeff_l0 P)).congr (Nat.sub_add_cancel hk) rfl fun Y => rfl
  refine (h1.add (leading_coeff_S21 P P.k (by omega))).congr rfl ?_ fun Y => rfl
  rw [add_zero, mul_neg, gg_zb_ggi]
end Formalism.FourierDecayAlt.P.Mx5

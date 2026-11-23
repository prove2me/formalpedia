-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.leading_coeff_t12
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:16.899037+00:00
-- url     : https://prove2.me/submissions/e93353f5-1804-441f-8392-02eac090e488

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_term_upper_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_term_lowering_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_gg_z_ggi
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
theorem _root_.solution (hk : 1 ≤ P.k) : Lead P.k (-zA P) (t12 P) := by
  have h1 := ((leading_coeff_t22 P).mul (leading_term_lowering_constant P)).congr (Nat.sub_add_cancel hk) rfl fun Y => rfl
  refine (h1.add (leading_term_upper_sum P P.k (by omega))).congr rfl ?_ fun Y => rfl
  rw [add_zero, mul_neg, gg_z_ggi]
end Formalism.FourierDecayAlt.P.Mx5

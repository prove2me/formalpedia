-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.leading_coeff_S4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:28.261649+00:00
-- url     : https://prove2.me/submissions/d47f7b6e-aa2b-4f63-b006-76a126313bd2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_const_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lead_xEx

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
theorem _root_.solution (m : ℕ) (hm : P.k - 1 < m) : Lead m (0 : A P) (S4 P) := by
  refine (Lead.sum (Icc 1 (P.k - 1)) (fun l Y => ∑ j ∈ (Icc 1 (P.k - 1)).erase l,
      star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π Y) fun l _ => ?_).congr rfl rfl fun Y => rfl
  refine Lead.sum _ (fun j Y => star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π Y) fun j _ => ?_
  exact ((lead_xEx P {l, j} m hm).const_mul (star (SS P l) * SS P j)).congr rfl (mul_zero _) fun Y => rfl
end Formalism.FourierDecayAlt.P.Mx5

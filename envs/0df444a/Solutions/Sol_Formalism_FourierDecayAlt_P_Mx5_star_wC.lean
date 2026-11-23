-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.star_wC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:11.386595+00:00
-- url     : https://prove2.me/submissions/d65aeee1-6985-476d-8bfb-3d7279d1443d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_conj_two
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_coordinate_polynomial_monic

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
theorem _root_.solution (π : Ty P) (Y : ℂ) : star (wC P π Y) = wC P π (star Y) := by
  have h1 : (wNum P π).map (starRingEnd ℂ) = wNum P π := by
    simp [wNum, qP, Polynomial.map_sum, Polynomial.map_prod, conj_two]
  have h2 : (coordinatePolynomial P π).map (starRingEnd ℂ) = coordinatePolynomial P π := by simp [coordinatePolynomial, Polynomial.map_prod]
  have h3 : (wNum P π /ₘ coordinatePolynomial P π).map (starRingEnd ℂ) = wNum P π /ₘ coordinatePolynomial P π := by
    rw [Polynomial.map_divByMonic _ (coordinate_polynomial_monic P π), h1, h2]
  show (starRingEnd ℂ) ((wNum P π /ₘ coordinatePolynomial P π).eval Y) = (wNum P π /ₘ coordinatePolynomial P π).eval ((starRingEnd ℂ) Y)
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, h3]
end Formalism.FourierDecayAlt.P.Mx5

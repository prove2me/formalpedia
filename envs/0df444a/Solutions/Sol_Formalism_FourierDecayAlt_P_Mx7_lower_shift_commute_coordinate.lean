-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.lower_shift_commute_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:58.639091+00:00
-- url     : https://prove2.me/submissions/8c87270a-4059-429d-b975-dd5ff1dfe4f1

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xC_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xEx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_rho_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absUX
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_fac_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fac_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xEx_up


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSh : SSShift) (hR : RhoUp) (P : Par) (Y : ℂ) (h0 : ∀ π, xC P π Y ≠ 0)
    (h1 : ∀ π, xC P π (Y + 1) ≠ 0) : Ul P Y * xA P (Y + 1) = xA P (Y + 1) * Ul P (Y + 1) := by
  unfold Ul
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have s1 : (kap P fun π => xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) * SS P j = SS P j * xA P (Y + 1) :=
    hSh P j _ _ (fun π π' hU => by
      show xEx P {j} π' (Y + 1) * (Y + (rho P π' j : ℂ)) = xC P π (Y + 1)
      rw [xC_eq P π (Y + 1) j hj, xEx_up hR P j π π' hU {j} (Finset.mem_singleton_self j), rho_up hR P j hj π π' hU]
      push_cast; ring)
  have s2 : (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * (kap P fun π => xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) =
      kap P fun π => xEx P {j} π (Y + 1) :=
    kap_mul P _ _ _ (fun π => by
      show (Y + (rho P π j : ℂ))⁻¹ * (xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) = xEx P {j} π (Y + 1)
      have := fac_ne P π Y j hj (h0 π)
      field_simp)
  have s3 : xA P (Y + 1) * (kap P fun π => (Y + 1 + (rho P π j : ℂ))⁻¹) = kap P fun π => xEx P {j} π (Y + 1) :=
    kap_mul P _ _ _ (fun π => by
      show xC P π (Y + 1) * (Y + 1 + (rho P π j : ℂ))⁻¹ = xEx P {j} π (Y + 1)
      have := fac_ne P π (Y + 1) j hj (h1 π)
      rw [xC_eq P π (Y + 1) j hj]; field_simp)
  exact absUX _ _ _ _ _ _ s1 s2 s3
end Formalism.FourierDecayAlt.P.Mx7

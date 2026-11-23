-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.monodromy_diagonal_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:18.926276+00:00
-- url     : https://prove2.me/submissions/d62b855b-a101-4cb9-8b3a-e310ad9730df

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_mul


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
theorem _root_.solution (hLF : LevFns) (P : Par) (Y : ℂ) (h : ∀ π, xC P π Y ≠ 0) :
    t22 P Y * ti P Y = 1 ∧ ti P Y * t22 P Y = 1 := by
  obtain ⟨_, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P
  have hX : xA P Y * (kap P fun π => (xC P π Y)⁻¹) = 1 :=
    (kap_mul P _ _ (fun _ => 1) (fun π => mul_inv_cancel₀ (h π))).trans (map_one (kap P))
  have hX' : (kap P fun π => (xC P π Y)⁻¹) * xA P Y = 1 :=
    (kap_mul P _ _ (fun _ => 1) (fun π => inv_mul_cancel₀ (h π))).trans (map_one (kap P))
  exact absInv _ _ _ _ hGGi hGiG hX hX' (kap_comm_sc P _ _) (kap_comm_sc P _ _)
end Formalism.FourierDecayAlt.P.Mx7

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.natDegree_q1_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:15.087483+00:00
-- url     : https://prove2.me/submissions/0eb59422-5ce7-4b97-9a98-ab0b47509422

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) : (q1P P).natDegree = 2 * P.k := by
  unfold q1P
  rw [natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  have : ∀ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2 := by
    intro i _
    rw [Monic.natDegree_mul (monic_X_add_C _) (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
  rw [Finset.sum_congr rfl this]
  simp [mul_comm]
end Formalism.FourierDecayAlt.P.Mx7

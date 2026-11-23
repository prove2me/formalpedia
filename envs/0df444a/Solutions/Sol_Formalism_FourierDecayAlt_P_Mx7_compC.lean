-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.compC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:21.866054+00:00
-- url     : https://prove2.me/submissions/18b51573-3755-42f0-93f2-f2e2b82024fe

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sum_anti
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_compC_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_compC_off

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
theorem _root_.solution (hSh : SSShift) (hC : SSComm) (hR : RhoUp) (P : Par) (hP : P.OK) (u v : ℂ) :
    weightedSumBis P u * weightedSumBis P v = weightedSumBis P v * weightedSumBis P u := by
  unfold weightedSumBis
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  apply sum_anti
  intro l hl j hj
  by_cases hjl : j = l
  · subst hjl
    rw [compC_diag hSh hR P u v j, sub_self, add_zero]
  · exact compC_off hSh hC hR P hP u v l j hl hj hjl
end Formalism.FourierDecayAlt.P.Mx7

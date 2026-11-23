-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.qC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:19.323287+00:00
-- url     : https://prove2.me/submissions/e253c103-8c37-450c-9d76-b652997e72ea

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr


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
theorem _root_.solution (P : Par) (Y : ℂ) : qC P Y = -((P.T : ℂ) * P.T') * (q1P P).eval Y := by
  unfold qC q1P
  simp only [eval_prod, eval_mul, eval_add, eval_X, eval_C]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by ring)
end Formalism.FourierDecayAlt.P.Mx7

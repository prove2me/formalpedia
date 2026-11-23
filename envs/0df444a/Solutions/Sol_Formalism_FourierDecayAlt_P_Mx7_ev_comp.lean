-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.ev_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:41.303406+00:00
-- url     : https://prove2.me/submissions/6238047a-a0a3-44a6-b293-2ebcf124f65e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_ev_C
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_ev_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_ev_monomial
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_add


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
variable {B : Type} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (Y c : ℂ) (p : B[X]) : ev Y (p.comp (X + C (algebraMap ℂ B c))) = ev (Y + c) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, map_add, map_add, hp, hq]
  | monomial n a => rw [monomial_comp, map_mul, map_pow, map_add, ev_C, ev_X, ev_C, ev_monomial, map_add]
end Formalism.FourierDecayAlt.P.Mx7

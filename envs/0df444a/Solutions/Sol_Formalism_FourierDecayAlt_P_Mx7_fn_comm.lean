-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.fn_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:27.857668+00:00
-- url     : https://prove2.me/submissions/136b586c-1d02-4aad-8190-8ff72801b6e3

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_scalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_comm


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
theorem _root_.solution (P : Par) (f fb g gb : Fn P.r) : Commute (sc P (fnP f fb)) (sc P (fnP g gb)) := by
  show sc P _ * sc P _ = sc P _ * sc P _
  have h : ∀ a b : Pr P.r, sc P a * sc P b = sc P (a * b) := fun a b => (map_mul (Matrix.scalar (Ty P)) a b).symm
  rw [h, h, Mx2.multiplierPair_comm]
end Formalism.FourierDecayAlt.P.Mx7

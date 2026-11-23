-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.IsPoly.ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:46.183919+00:00
-- url     : https://prove2.me/submissions/f7bfb0e2-d4c2-46a0-89af-de737be26ecd

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_eq_zero

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
namespace IsPoly
theorem _root_.solution {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) {S : Set ℂ} (hS : S.Finite)
    (h : ∀ Y, Y ∉ S → F Y = G Y) (Y : ℂ) : F Y = G Y :=
  sub_eq_zero.1 ((hF.sub hG).eq_zero hS (fun Z hZ => sub_eq_zero.2 (h Z hZ)) Y)
end IsPoly
end Formalism.FourierDecayAlt.P.Mx7

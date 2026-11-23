-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.IsPoly.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:28.918817+00:00
-- url     : https://prove2.me/submissions/22e11932-b72b-4a61-848e-8509b03ad051

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity

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
theorem _root_.solution {F G : ℂ → B} (hF : IsPoly F) (h : ∀ Y, G Y = F Y) : IsPoly G := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨p, fun Y => by rw [h, hp]⟩
end IsPoly
end Formalism.FourierDecayAlt.P.Mx7

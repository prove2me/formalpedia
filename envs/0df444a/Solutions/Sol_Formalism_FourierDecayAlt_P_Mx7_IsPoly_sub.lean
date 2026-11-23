-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.IsPoly.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:39.547014+00:00
-- url     : https://prove2.me/submissions/672a680f-5042-456f-9acc-15d565dad7ae

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
theorem _root_.solution {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) : IsPoly (fun Y => F Y - G Y) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p - q, fun Y => by show F Y - G Y = _; rw [map_sub, hp, hq]⟩
end IsPoly
end Formalism.FourierDecayAlt.P.Mx7

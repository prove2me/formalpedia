-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.IsPoly.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:04.299964+00:00
-- url     : https://prove2.me/submissions/fcfb36f6-71cf-4101-9b65-085b5a040a4c

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
theorem _root_.solution {F : ℂ → B} (hF : IsPoly F) : IsPoly (fun Y => -F Y) := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨-p, fun Y => by show -F Y = _; rw [map_neg, hp]⟩
end IsPoly
end Formalism.FourierDecayAlt.P.Mx7

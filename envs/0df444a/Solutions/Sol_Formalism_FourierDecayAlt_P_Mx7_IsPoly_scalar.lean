-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.IsPoly.scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:53.713291+00:00
-- url     : https://prove2.me/submissions/6a5f3ade-4730-4a2d-a3cc-6bba8fd931a4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_ev_apply

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
theorem _root_.solution (p : ℂ[X]) : IsPoly (fun Y => algebraMap ℂ B (p.eval Y)) :=
  ⟨p.map (algebraMap ℂ B), fun Y => by rw [ev_apply, eval₂_map, RingHom.id_comp, eval₂_at_apply]⟩
end IsPoly
end Formalism.FourierDecayAlt.P.Mx7

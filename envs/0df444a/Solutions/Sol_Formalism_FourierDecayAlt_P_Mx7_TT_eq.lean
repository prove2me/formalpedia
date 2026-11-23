-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.TT_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:38.924484+00:00
-- url     : https://prove2.me/submissions/8cb80066-260f-4e70-99c6-2638616dda39

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
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (l j : ℕ) (f g f' : Ty P → ℂ) (h : kap P f * SS P j = SS P j * kap P f') :
    (SS P l * kap P f) * (SS P j * kap P g) = SS P l * SS P j * kap P (f' * g) := by
  rw [map_mul]
  calc (SS P l * kap P f) * (SS P j * kap P g) = SS P l * (kap P f * SS P j) * kap P g := by
        simp only [mul_assoc]
    _ = _ := by rw [h]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Mx7

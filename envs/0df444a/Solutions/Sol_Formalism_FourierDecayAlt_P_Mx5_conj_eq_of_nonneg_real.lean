-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.conj_eq_of_nonneg_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:08.644813+00:00
-- url     : https://prove2.me/submissions/1a02f069-04bb-400a-b53e-ef2a89e6a3e6

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution {R : Type*} [Ring R] (g gi x M L : R) (h2 : gi * g = 1)
    (e1 : gi * (x * g) = x) (hxM : Commute x M) (hxL : Commute x L) :
    g * M * gi * (g * L * gi * (x * g)) = g * x * M * L := by
  calc g * M * gi * (g * L * gi * (x * g)) = g * M * (gi * g) * L * (gi * (x * g)) := by
        simp only [mul_assoc]
    _ = g * (M * L * x) := by
        rw [h2, e1, mul_one]
        simp only [mul_assoc]
    _ = g * x * M * L := by
        rw [(hxM.mul_right hxL).symm.eq]
        simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Mx5

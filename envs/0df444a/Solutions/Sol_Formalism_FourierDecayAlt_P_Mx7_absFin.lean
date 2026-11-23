-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absFin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:50.198797+00:00
-- url     : https://prove2.me/submissions/c21add5b-a210-4e40-914c-4379e5c1ae90

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
variable {R : Type*} [Ring R] [Algebra ℂ R]
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (Gi K S : R) (c : ℂ) (h : Commute K Gi) :
    K * Gi * Gi + c • (Gi * Gi) + Gi * Gi * S = Gi * Gi * (K + c • 1 + S) := by
  have : K * Gi * Gi = Gi * Gi * K := by rw [h.eq, mul_assoc, h.eq, mul_assoc]
  rw [this, mul_add, mul_add, mul_smul_comm, mul_one]
end Formalism.FourierDecayAlt.P.Mx7

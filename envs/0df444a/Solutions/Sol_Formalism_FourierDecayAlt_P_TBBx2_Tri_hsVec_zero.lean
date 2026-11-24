-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:31.249879+00:00
-- url     : https://prove2.me/submissions/a705aa4e-8657-43d9-80dc-b793df2133aa

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Tri
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.TBBx2.Tri
theorem _root_.solution : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  ext i
  simp [B.hsVec]
end Formalism.FourierDecayAlt.P.TBBx2.Tri

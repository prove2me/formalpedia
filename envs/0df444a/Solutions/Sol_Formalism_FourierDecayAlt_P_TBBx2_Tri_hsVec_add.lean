-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:29.708417+00:00
-- url     : https://prove2.me/submissions/005d67ed-d759-4198-8762-4e96bec31925

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
theorem _root_.solution (A A' : Wq →L[ℂ] Wp) : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
  ext i
  simp [B.hsVec]
end Formalism.FourierDecayAlt.P.TBBx2.Tri

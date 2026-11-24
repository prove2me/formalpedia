-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:41:02.609147+00:00
-- url     : https://prove2.me/submissions/7c044c2e-a28c-4fc6-aded-1691b63a9e9d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsVecApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_HilbertSchmidtVectorization_conjE_hsVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization
theorem _root_.solution (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A B : Wq →L[ℂ] Wp) :
    hsInner (T A) B = hsInner A (adjH T B) := by
  unfold hsInner
  rw [hsE_adjH, ContinuousLinearMap.adjoint_inner_left, conjE_hsVec]
end Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization

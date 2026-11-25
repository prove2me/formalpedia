-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjR_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:31:17.787805+00:00
-- url     : https://prove2.me/submissions/635d219f-ef22-4cc3-9c68-e766583b714b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsVecApply

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
theorem _root_.solution (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjR T = adjH T := rfl
end Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization

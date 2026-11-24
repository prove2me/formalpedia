-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.conjE_hsVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:19:43.623159+00:00
-- url     : https://prove2.me/submissions/948f9d6a-3c0f-4661-8edf-26b2c2230236

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
theorem _root_.solution (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A : Wq →L[ℂ] Wp) :
    conjE T (hsVec A) = hsVec (T A) := by
  show hsE (T (hsE.symm (hsE A))) = _
  rw [LinearEquiv.symm_apply_apply]; rfl
end Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization

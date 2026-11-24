-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c7_form_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:45:17.503901+00:00
-- url     : https://prove2.me/submissions/f2c24aec-6b85-48e1-977d-d6dd60593522

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TorusArgumentMultiplicative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate InnerProductSpace ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.FormMono := by
  intro ι _ _ H _ _ V K K' hA
  have hG : ((Matrix.gram ℂ V)ᵀ).PosSemidef := (Matrix.posSemidef_gram (𝕜 := ℂ) V).transpose
  have hM := hA.hadamard hG
  have := hM.dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  simpa [dotProduct, mulVec, Matrix.hadamard_apply, Matrix.gram_apply, Matrix.transpose_apply] using this
end Formalism.FourierDecayAlt.P

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.enorm_smulRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:19:19.551187+00:00
-- url     : https://prove2.me/submissions/3e388bfa-8652-43ea-a8b2-65832be4df84

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNMulRpow
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (a : E) (b : F) :
    ‖(innerSL ℂ a).smulRight b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, ENNReal.ofReal_mul (norm_nonneg _)]
end Formalism.FourierDecayAlt.P.S3dx4

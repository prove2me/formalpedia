-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.inner_self_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:30:53.533798+00:00
-- url     : https://prove2.me/submissions/2ec3124a-f864-41cc-9bfa-9bfb39945eba

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution (a : Wp) : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) a
  · rw [Complex.ofReal_im]
    exact inner_self_im (𝕜 := ℂ) a
end Formalism.FourierDecayAlt.P.DDSmoothness

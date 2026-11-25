-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.measurable_enorm_composition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:02:10.771941+00:00
-- url     : https://prove2.me/submissions/1ebc9c9f-9a56-4c5c-99ee-c0d2a82a6fa0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableEnormComposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_mt_cont


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
theorem _root_.solution {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) : Measurable (fun t => ‖e0 (Matrix.of (f t))‖ₑ) :=
  ((he0.comp mt_cont).measurable.comp hf).enorm
end Formalism.FourierDecayAlt.P.S3dx4

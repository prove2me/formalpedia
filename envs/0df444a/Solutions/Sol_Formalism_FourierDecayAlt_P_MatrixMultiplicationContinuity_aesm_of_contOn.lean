-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.aesm_of_contOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:30:13.67705+00:00
-- url     : https://prove2.me/submissions/d1b681c6-7ce8-454e-a47f-07bc10c80ba0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReproducingFormulaReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
theorem _root_.solution {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] [NormedAddCommGroup E] [SecondCountableTopology E]
    {μ : Measure α} {f : α → E} {s : Set α} (hf : ContinuousOn f s) (hs : MeasurableSet s)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) : AEStronglyMeasurable f μ := by
  have h := hf.aestronglyMeasurable hs (μ := μ)
  rwa [Measure.restrict_eq_self_of_ae_mem hμ] at h
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

-- Prove2me | solution 1 for Formalism.IndefR.Tow.SobPf.Avg.ae_mem_of_compl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:27.548887+00:00
-- url     : https://prove2.me/submissions/fc3aa059-f810-4006-a160-7163ac09579e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_HasFDerivAtIntegralPIter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open Formalism Formalism.IndefR Formalism.IndefR.Tow Formalism.IndefR.Tow.SobPf Formalism.IndefR.Tow.SobPf.Avg
variable {m : ℕ} {X E : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [SecondCountableTopology X] [OpensMeasurableSpace X] [NormedSpace ℝ E] [CompleteSpace E]
namespace Formalism.IndefR.Tow.SobPf.Avg
theorem _root_.solution {μ : Measure X} {K : Set X} (hμK : μ Kᶜ = 0) : ∀ᵐ x ∂μ, x ∈ K := mem_ae_iff.2 hμK
end Formalism.IndefR.Tow.SobPf.Avg

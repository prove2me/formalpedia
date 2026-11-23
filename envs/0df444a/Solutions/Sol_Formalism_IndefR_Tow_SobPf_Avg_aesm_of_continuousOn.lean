-- Prove2me | solution 1 for Formalism.IndefR.Tow.SobPf.Avg.aesm_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:12.743722+00:00
-- url     : https://prove2.me/submissions/b882aff4-715b-429e-a239-895c734b7ee7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_HasFDerivAtIntegralPIter
import Theorems.Thm_Formalism_IndefR_Tow_SobPf_Avg_ae_mem_of_compl

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
omit [NormedSpace ℝ E] [CompleteSpace E]
namespace Formalism.IndefR.Tow.SobPf.Avg
theorem _root_.solution {μ : Measure X} {K : Set X} (hKm : MeasurableSet K) (hμK : μ Kᶜ = 0)
    {F : Type*} [NormedAddCommGroup F] {f : X → F} (hf : ContinuousOn f K) : AEStronglyMeasurable f μ := by
  have h := hf.aestronglyMeasurable (μ := μ) hKm
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_mem_of_compl hμK)] at h
end Formalism.IndefR.Tow.SobPf.Avg

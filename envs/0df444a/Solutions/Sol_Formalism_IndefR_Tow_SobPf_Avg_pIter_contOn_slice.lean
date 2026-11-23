-- Prove2me | solution 1 for Formalism.IndefR.Tow.SobPf.Avg.pIter_contOn_slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:12.955825+00:00
-- url     : https://prove2.me/submissions/ed70218d-5dce-4af6-b943-8ef03960655e

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
omit [CompleteSpace E]
namespace Formalism.IndefR.Tow.SobPf.Avg
theorem _root_.solution {K : Set X} {Φ : (Fin m → ℝ) → X → E} {j : ℕ}
    (hc : ContinuousOn (fun q : (Fin m → ℝ) × X => pIter Φ j q.1 q.2) (Set.univ ×ˢ K)) (t : Fin m → ℝ) :
    ContinuousOn (fun k => pIter Φ j t k) K :=
  hc.comp (by fun_prop : Continuous fun k : X => (t, k)).continuousOn
    (fun _ hk => Set.mk_mem_prod (Set.mem_univ _) hk)
end Formalism.IndefR.Tow.SobPf.Avg

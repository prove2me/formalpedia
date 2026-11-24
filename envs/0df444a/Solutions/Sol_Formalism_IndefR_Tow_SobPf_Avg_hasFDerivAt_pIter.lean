-- Prove2me | solution 1 for Formalism.IndefR.Tow.SobPf.Avg.hasFDerivAt_pIter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:21.925805+00:00
-- url     : https://prove2.me/submissions/897923b6-6f27-4ac9-b2a4-1cf5f612bfa5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_HasFDerivAtIntegralPIter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
namespace Formalism.IndefR.Tow.SobPf.Avg
variable {m : ℕ} {X E : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
private theorem natCast_lt_top_withTop_enat (j : ℕ) : (j : WithTop ℕ∞) < ∞ := by
  exact_mod_cast ENat.natCast_lt_top j
end Formalism.IndefR.Tow.SobPf.Avg
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open Formalism Formalism.IndefR Formalism.IndefR.Tow Formalism.IndefR.Tow.SobPf Formalism.IndefR.Tow.SobPf.Avg
variable {m : ℕ} {X E : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Formalism.IndefR.Tow.SobPf.Avg
theorem _root_.solution {Φ : (Fin m → ℝ) → X → E} {k : X} (hΦ : ContDiff ℝ ∞ fun t => Φ t k) (j : ℕ)
    (t : Fin m → ℝ) :
    HasFDerivAt (fun t => pIter Φ j t k)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Fin m → ℝ) E (pIter Φ (j + 1) t k)) t := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ j (fun t => Φ t k)) :=
    hΦ.differentiable_iteratedFDeriv (natCast_lt_top_withTop_enat j)
  have h2 := (hd t).hasFDerivAt
  rw [fderiv_iteratedFDeriv] at h2
  simpa [pIter] using h2
end Formalism.IndefR.Tow.SobPf.Avg

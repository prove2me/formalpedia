-- Prove2me | solution 1 for Formalism.FN.GjScaling.measurableSet_boxJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:49.29223+00:00
-- url     : https://prove2.me/submissions/5e168700-c7d7-4159-88e3-d564baefea1d

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
open Formalism.FN.GjScaling
variable {ι : Type*} [Fintype ι]
variable (n j : ℕ)
namespace Formalism.FN.GjScaling
theorem _root_.solution : MeasurableSet (boxJ n j) := by
  have : Formalism.FN.boxJ n j =
      ⋂ i : Fin n, ⋂ (_ : (i : ℕ) < j), (fun u : Fin n → ℝ => u i) ⁻¹' Set.Ico 0 1 := by
    ext u
    simp [Formalism.FN.boxJ]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurable_pi_apply i measurableSet_Ico
end Formalism.FN.GjScaling

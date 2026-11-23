-- Prove2me | solution 1 for Formalism.FN.GjScaling.tm_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:49.257078+00:00
-- url     : https://prove2.me/submissions/04c4fb36-054a-4e26-83c5-043e869344cf

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
namespace Formalism.FN.GjScaling
theorem _root_.solution : tm (∅ : Set (ι → ℝ)) = 0 := by
  simp [tm]
end Formalism.FN.GjScaling

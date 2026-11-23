-- Prove2me | solution 1 for Formalism.FN.GjScaling.tm_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:04.258628+00:00
-- url     : https://prove2.me/submissions/6577d9ca-961a-4b41-856e-1c25747041b8

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
theorem _root_.solution {B B' : Set (ι → ℝ)} (h : B ⊆ B') : tm B ≤ tm B' := by
  unfold tm
  exact measure_mono (Set.inter_subset_inter subset_rfl (Set.add_subset_add h subset_rfl))
end Formalism.FN.GjScaling

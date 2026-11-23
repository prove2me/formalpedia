-- Prove2me | solution 1 for Formalism.FN.GjScaling.Zv_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:48.313807+00:00
-- url     : https://prove2.me/submissions/e6a9ccee-9e47-4751-8b6e-2874c6626a19

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
theorem _root_.solution {a : ι → ℝ} (ha : a ∈ Zv ι) : -a ∈ Zv ι := fun i => by
  obtain ⟨m, hm⟩ := ha i
  exact ⟨-m, by rw [Pi.neg_apply, hm, Int.cast_neg]⟩
end Formalism.FN.GjScaling

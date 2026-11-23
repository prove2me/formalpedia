-- Prove2me | solution 1 for Formalism.FN.GjScaling.Zv_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:47.761118+00:00
-- url     : https://prove2.me/submissions/01c32447-84a8-4652-a457-1e1213baf428

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
theorem _root_.solution {a b : ι → ℝ} (ha : a ∈ Zv ι) (hb : b ∈ Zv ι) : a + b ∈ Zv ι := fun i => by
  obtain ⟨m, hm⟩ := ha i
  obtain ⟨m', hm'⟩ := hb i
  exact ⟨m + m', by rw [Pi.add_apply, hm, hm', Int.cast_add]⟩
end Formalism.FN.GjScaling

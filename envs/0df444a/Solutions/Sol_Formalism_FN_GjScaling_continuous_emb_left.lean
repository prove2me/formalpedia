-- Prove2me | solution 1 for Formalism.FN.GjScaling.continuous_emb_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:48.378696+00:00
-- url     : https://prove2.me/submissions/93933f7f-36b1-408b-b807-85abc5adc68f

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
theorem _root_.solution (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    Continuous fun u => emb n j u y := by
  refine continuous_pi fun i => ?_
  by_cases h : (i : ℕ) < j
  · simp only [emb, dif_pos h]
    exact continuous_apply _
  · simp only [emb, dif_neg h]
    exact continuous_const
end Formalism.FN.GjScaling

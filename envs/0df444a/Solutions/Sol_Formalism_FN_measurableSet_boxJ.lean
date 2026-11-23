-- Prove2me | solution 1 for Formalism.FN.measurableSet_boxJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:04.939021+00:00
-- url     : https://prove2.me/submissions/030b2c8c-847b-41f8-b45f-d8a8a4ccc3fb

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
namespace Formalism.FN
theorem _root_.solution (n j : ℕ) : MeasurableSet (boxJ n j) := by
  have h : boxJ n j = ⋂ i : Fin n, ⋂ (_ : (i : ℕ) < j),
      ({u : Fin n → ℝ | 0 ≤ u i} ∩ {u | u i < 1}) := by
    ext u; simp [boxJ]
  rw [h]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    (measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)
end Formalism.FN

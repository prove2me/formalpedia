-- Prove2me | solution 1 for Formalism.FN.GjScaling.fundamentalDomain_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:48.374068+00:00
-- url     : https://prove2.me/submissions/27a9ac65-2bb2-4c7f-851c-d8da36a627db

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
theorem _root_.solution : ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) = Qv ι := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, Pi.basisFun_repr, Set.mem_Ico, Qv, Set.mem_setOf_eq]
end Formalism.FN.GjScaling

-- Prove2me | solution 1 for Formalism.DivisionValues.mean_log_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:21.062233+00:00
-- url     : https://prove2.me/submissions/17d8d284-690a-4f06-b014-168dfb117e43

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues
theorem _root_.solution (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) :
    2 * ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Real.sqrt (t v))) = meanLog t := by
  unfold meanLog
  have h : ∑ v, Real.log (Real.sqrt (t v)) = (∑ v, Real.log (t v)) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => Real.log_sqrt (ht v).le
  rw [h]
  ring
end Formalism.DivisionValues

-- Prove2me | solution 1 for Formalism.DivisionValues.meanLog_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:19.976666+00:00
-- url     : https://prove2.me/submissions/a9bac1a0-78d2-4ada-9d5f-e535106dc735

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
theorem _root_.solution (t κ : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) (hκ : ∀ v, 0 < κ v) :
    meanLog (fun v => t v * κ v) = meanLog t + meanLog κ := by
  unfold meanLog
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun v _ => Real.log_mul (ht v).ne' (hκ v).ne'
end Formalism.DivisionValues

-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.budget_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:44.248642+00:00
-- url     : https://prove2.me/submissions/33c8e552-c5e6-48f0-8180-badc0694f10b

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.EigenvalueLevelCeiling
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : BudgetNum := by
  unfold BudgetNum
  intro dK δq D B hδ hD hB hq
  rw [div_le_iff₀ (mul_pos hδ hD)]
  have h1 : dK ≤ 3 * D * δq := (div_le_iff₀ hδ).mp hq
  have h2 : dK * B ≤ 3 * D * δq * B := mul_le_mul_of_nonneg_right h1 hB
  linarith
end Formalism.EigenvalueLevelCeiling

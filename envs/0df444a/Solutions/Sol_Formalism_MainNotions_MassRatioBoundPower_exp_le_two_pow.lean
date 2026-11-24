-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioBoundPower.exp_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:39.527962+00:00
-- url     : https://prove2.me/submissions/a208abe8-a1d6-48d0-839d-039ef51f800b

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioBoundPower
open NumberField Formalism.MainNotions.MassRatioZetaBound
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioBoundPower
theorem _root_.solution : Real.exp (4 * zetaGL3GL2) ≤ 2 ^ cZ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : (2 : ℝ) ^ cZ = Real.exp ((cZ : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e]
  apply Real.exp_le_exp.2
  calc 4 * zetaGL3GL2 = (4 * zetaGL3GL2 / Real.log 2) * Real.log 2 := by field_simp
    _ ≤ (cZ : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hl.le
end Formalism.MainNotions.MassRatioBoundPower

-- Prove2me | solution 1 for CCRuleCW.sup_le_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:40:59.92581+00:00
-- url     : https://prove2.me/submissions/cc35e8c9-9fff-4123-93c5-5800d0e58fdb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_entry_le_gN


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace CCRuleCW
theorem _root_.solution (g : B.Mat k r) : ‖g‖ ≤ B.gN g :=
  (Matrix.norm_le_iff (Real.sqrt_nonneg _)).2 fun i j => entry_le_gN g i j
end CCRuleCW

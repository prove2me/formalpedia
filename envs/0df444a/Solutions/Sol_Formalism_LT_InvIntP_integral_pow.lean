-- Prove2me | solution 1 for Formalism.LT.InvIntP.integral_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:33.632817+00:00
-- url     : https://prove2.me/submissions/7cff52d2-6925-4900-b244-2e17035dea42

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_integral_mul
import Theorems.Thm_Formalism_LT_InvIntP_integral_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
namespace Formalism.LT.InvIntP
theorem _root_.solution {A : MvPowerSeries ι K} (hA : IntegralMv A) (n : ℕ) :
    IntegralMv (A ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact integral_one
  | succ n ih =>
    rw [pow_succ]
    exact integral_mul ih hA
end Formalism.LT.InvIntP

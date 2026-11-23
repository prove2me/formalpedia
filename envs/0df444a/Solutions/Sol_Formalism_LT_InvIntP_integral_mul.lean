-- Prove2me | solution 1 for Formalism.LT.InvIntP.integral_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:45.763632+00:00
-- url     : https://prove2.me/submissions/7e4ecf1c-55b9-47aa-81ea-70ace4f2755c

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt

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
theorem _root_.solution {A B : MvPowerSeries ι K} (hA : IntegralMv A) (hB : IntegralMv B) :
    IntegralMv (A * B) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun ab _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _) (norm_nonneg _) (hB _)
end Formalism.LT.InvIntP

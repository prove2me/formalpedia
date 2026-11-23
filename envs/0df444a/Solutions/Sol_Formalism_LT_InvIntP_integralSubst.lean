-- Prove2me | solution 1 for Formalism.LT.InvIntP.integralSubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:10.387569+00:00
-- url     : https://prove2.me/submissions/366139d4-95c6-4bdf-b6f5-99ce0e0ba1c5

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_integral_pow

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
theorem _root_.solution (f : PowerSeries K) (P : MvPowerSeries ι K)
    (hf : IntegralPS f) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    IntegralMv (f.subst P) := by
  intro e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hP0)]
  by_cases hfin : (Function.support fun n : ℕ => PowerSeries.coeff n f • MvPowerSeries.coeff e (P ^ n)).Finite
  · rw [finsum_eq_sum _ hfin]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
    rw [norm_smul]
    exact mul_le_one₀ (hf n) (norm_nonneg _) (integral_pow hP n e)
  · rw [finsum_of_infinite_support hfin, norm_zero]
    exact zero_le_one
end Formalism.LT.InvIntP

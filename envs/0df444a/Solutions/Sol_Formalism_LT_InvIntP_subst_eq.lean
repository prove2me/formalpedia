-- Prove2me | solution 1 for Formalism.LT.InvIntP.subst_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:25.394555+00:00
-- url     : https://prove2.me/submissions/e051c63c-d2b8-4532-a7c6-2c48d6dc4d7c

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_decomp

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
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.LT.InvIntP
theorem _root_.solution (f : PowerSeries K) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    {a : MvPowerSeries ι K} (ha0 : MvPowerSeries.constantCoeff a = 0) :
    f.subst a = a + a ^ 2 * (tail2 f).subst a := by
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  conv_lhs => rw [decomp f h0 h1]
  rw [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]
end Formalism.LT.InvIntP

-- Prove2me | solution 1 for Formalism.LT.LTL.divBy_psubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:30.243821+00:00
-- url     : https://prove2.me/submissions/47a10371-20d2-47e8-a477-99f9aa8bd937

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_P2M_Formalism_LT_LTL_norm_finsum_le__8658a123f7be
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
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution (c : K) (f : PowerSeries K) (P : MvPowerSeries ι K)
    (hf : DivBy c f) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv c (f.subst P) := by
  intro d
  have ha : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.coeff_subst ha f d]
  refine norm_finsum_le' (norm_nonneg _) fun n => ?_
  rw [smul_eq_mul, norm_mul]
  calc _ ≤ ‖c‖ * 1 := mul_le_mul (hf n) (integral_pow hP n d) (norm_nonneg _) (norm_nonneg _)
    _ = ‖c‖ := mul_one _
end Formalism.LT.LTL

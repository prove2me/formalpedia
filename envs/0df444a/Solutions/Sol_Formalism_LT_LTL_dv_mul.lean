-- Prove2me | solution 1 for Formalism.LT.LTL.dv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:32.744334+00:00
-- url     : https://prove2.me/submissions/fe26a1fd-a258-4a6c-8a3e-2b6f88ee9397

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma

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
theorem _root_.solution {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : IntegralMv B) :
    DivByMv c (A * B) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun p _ => ?_
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 A‖ * ‖MvPowerSeries.coeff p.2 B‖ ≤ ‖c‖ * 1 :=
        mul_le_mul (hA _) (hB _) (norm_nonneg _) (norm_nonneg _)
    _ = ‖c‖ := mul_one _
end Formalism.LT.LTL

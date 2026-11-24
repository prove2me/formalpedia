-- Prove2me | solution 1 for Formalism.LT.LTL.integral_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:36.606236+00:00
-- url     : https://prove2.me/submissions/6846cd4e-7b89-4c31-84d5-f47a1935ed5c

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_coeff_lin

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
variable [Fintype ι] [DecidableEq ι]
namespace Formalism.LT.LTL
theorem _root_.solution (a : ι → K) (ha : ∀ i, ‖a i‖ ≤ 1) : IntegralMv (lin a) := by
  intro d
  rw [coeff_lin]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  split_ifs <;> simp [ha i]
end Formalism.LT.LTL

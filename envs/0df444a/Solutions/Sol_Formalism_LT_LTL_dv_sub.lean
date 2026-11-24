-- Prove2me | solution 1 for Formalism.LT.LTL.dv_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:29.307416+00:00
-- url     : https://prove2.me/submissions/f23428c0-f16b-4716-964c-19fe98b58758

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_dv_add
import Theorems.Thm_Formalism_LT_LTL_dv_neg

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
theorem _root_.solution {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : DivByMv c B) :
    DivByMv c (A - B) := by rw [sub_eq_add_neg]; exact dv_add hA (dv_neg hB)
end Formalism.LT.LTL

-- Prove2me | solution 1 for Formalism.LT.LTL.Cong.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:41.516669+00:00
-- url     : https://prove2.me/submissions/0dd958a4-df98-45f4-a245-000572138257

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_dv_add
import Theorems.Thm_Formalism_LT_LTL_dv_mul
import Theorems.Thm_Formalism_LT_InvIntP_integral_mul


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
namespace Cong
theorem _root_.solution {c : K} {A B C D : MvPowerSeries ι K} (h1 : Cong c A B) (h2 : Cong c C D) :
    Cong c (A * C) (B * D) := by
  refine ⟨integral_mul h1.1 h2.1, integral_mul h1.2.1 h2.2.1, ?_⟩
  have e : A * C - B * D = (A - B) * C + (C - D) * B := by ring
  rw [e]
  exact dv_add (dv_mul h1.2.2 h2.1) (dv_mul h2.2.2 h1.2.1)
end Cong
end Formalism.LT.LTL

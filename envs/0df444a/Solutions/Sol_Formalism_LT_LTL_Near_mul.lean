-- Prove2me | solution 1 for Formalism.LT.LTL.Near.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:56.544952+00:00
-- url     : https://prove2.me/submissions/1e624b36-57f6-453f-8023-1116ef5a07bd

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_LT_InvIntP_Low_add
import Theorems.Thm_Formalism_LT_InvIntP_Low_mono
import Theorems.Thm_Formalism_LT_InvIntP_Low_mul


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
variable {K : Type u} [NormedField K] {ι : Type*}
namespace Formalism.LT.LTL
namespace Near
theorem _root_.solution {k l : ℕ} {A B C D : MvPowerSeries ι K} (h1 : Near k A B) (h2 : Near l C D) :
    Near (k + l) (A * C) (B * D) := by
  refine ⟨h1.1.mul h2.1, h1.2.1.mul h2.2.1, ?_⟩
  have e : A * C - B * D = (A - B) * C + B * (C - D) := by ring
  rw [e]
  exact ((h1.2.2.mul h2.1).mono (by omega)).add ((h1.2.1.mul h2.2.2).mono (by omega))
end Near
end Formalism.LT.LTL

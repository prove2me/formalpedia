-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaLog.wFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:24:51.379828+00:00
-- url     : https://prove2.me/submissions/3fe443fc-f953-454a-940c-4caf6545a15b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaLog
namespace Formalism.L2.Th1.F.SigmaLog
theorem _root_.solution {l z : ℂ} (h : z ≠ l) : wFactor l z ≠ 0 := by
  unfold wFactor
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  by_cases hl : l = 0
  · simp [hl]
  · intro h0
    apply h
    field_simp at h0
    linear_combination -h0
end Formalism.L2.Th1.F.SigmaLog

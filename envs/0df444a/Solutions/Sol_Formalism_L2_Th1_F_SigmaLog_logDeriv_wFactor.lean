-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaLog.logDeriv_wFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:25:06.769806+00:00
-- url     : https://prove2.me/submissions/216fd6ba-888b-456e-ba02-fe70128f7cfd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaLog
import Theorems.Thm_Formalism_L2_Th1_F_SigmaLog_hasDerivAt_wFactor

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
theorem _root_.solution {l z : ℂ} (h : z ≠ l) :
    logDeriv (wFactor l) z
      = (1 / (z - l) + 1 / l + z / l ^ 2) - (if l = 0 then 1 / z else 0) := by
  rw [logDeriv_apply, (hasDerivAt_wFactor l z).deriv]
  by_cases hl : l = 0
  · simp [hl, wFactor]
  · have h1 : z - l ≠ 0 := sub_ne_zero.mpr h
    have h2 : 1 - z / l ≠ 0 := by
      intro h0
      apply h
      field_simp at h0
      linear_combination -h0
    have h3 : l - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have he := Complex.exp_ne_zero (z / l + z ^ 2 / (2 * l ^ 2))
    rw [if_neg hl, wFactor, sub_zero, div_eq_iff (mul_ne_zero h2 he)]
    field_simp
    ring
end Formalism.L2.Th1.F.SigmaLog

-- Prove2me | solution 1 for Formalism.L2.Th1.F.Taylor.taylor0_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:38:59.722087+00:00
-- url     : https://prove2.me/submissions/7f18cdde-4ff4-4e65-b872-23a5d9b9ab84

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_coeff_taylor0
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_iteratedDeriv_comp_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Taylor
open PowerSeries
namespace Formalism.L2.Th1.F.Taylor
theorem _root_.solution {f : ℂ → ℂ} (a : ℂ) (hf : AnalyticAt ℂ f 0) :
    taylor0 (fun z => f (a * z)) = rescale a (taylor0 f) := by
  ext n
  rw [coeff_rescale, coeff_taylor0, coeff_taylor0, iteratedDeriv_comp_mul a n f hf, mul_div_assoc]
end Formalism.L2.Th1.F.Taylor

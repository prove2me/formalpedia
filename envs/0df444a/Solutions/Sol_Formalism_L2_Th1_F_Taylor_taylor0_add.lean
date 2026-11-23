-- Prove2me | solution 1 for Formalism.L2.Th1.F.Taylor.taylor0_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:43.991059+00:00
-- url     : https://prove2.me/submissions/c889d51c-7337-414c-b36d-48a8f26f0d2e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_coeff_taylor0

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
theorem _root_.solution {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor0 (fun z => f z + g z) = taylor0 f + taylor0 g := by
  ext n
  rw [map_add, coeff_taylor0, coeff_taylor0, coeff_taylor0,
    iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]
end Formalism.L2.Th1.F.Taylor

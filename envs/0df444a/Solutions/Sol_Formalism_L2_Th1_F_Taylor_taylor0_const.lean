-- Prove2me | solution 1 for Formalism.L2.Th1.F.Taylor.taylor0_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:43.959527+00:00
-- url     : https://prove2.me/submissions/226ea045-ad5a-4e17-a7f2-e99fd717e575

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
theorem _root_.solution (c : ℂ) : taylor0 (fun _ => c) = C c := by
  ext n
  rw [coeff_taylor0, iteratedDeriv_const, coeff_C]
  split_ifs with h
  · simp [h]
  · simp
end Formalism.L2.Th1.F.Taylor

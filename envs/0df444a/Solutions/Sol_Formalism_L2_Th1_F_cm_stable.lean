-- Prove2me | solution 1 for Formalism.L2.Th1.F.cm_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:26:16.244879+00:00
-- url     : https://prove2.me/submissions/1da7cf88-911e-46e3-918f-3809198507e3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_theta_sq
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_mem_iff

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
open Cm1
namespace Formalism.L2.Th1.F
theorem _root_.solution : CmStable := by
  intro a b c d ha hd h m n z hz
  have hsq := Formalism.L2.Th1.F.Cm1.theta_sq a b c d h
  obtain ⟨x, y, rfl⟩ := (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd z).mp hz
  refine (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mpr ⟨m * x - n * y * c, m * y + n * x * a + n * y * b, ?_⟩
  push_cast
  linear_combination (-((n : ℂ) * (y : ℂ))) * hsq
end Formalism.L2.Th1.F

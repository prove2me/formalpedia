-- Prove2me | solution 1 for Formalism.L2.Th1.F.cmQuasiPeriodConst_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:25:35.661296+00:00
-- url     : https://prove2.me/submissions/73ffe5d9-f5f3-482d-bea6-01bd52d81b1a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny

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
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : QuasiPeriodConstIsogeny) : CMQuasiPeriodConst := by
  intro L α S hst him hS
  have hα : α ≠ 0 := by
    intro h0
    apply him
    rw [h0]
    simp
  have h1 := h L α S hα hst hS
  have hsub : α - conj α ≠ 0 := by
    intro h0
    apply him
    have h2 := congrArg Complex.im h0
    simp at h2
    linarith
  rw [← Complex.mul_conj] at h1
  rw [eq_div_iff (mul_ne_zero hα hsub)]
  linear_combination h1
end Formalism.L2.Th1.F

-- Prove2me | solution 1 for Formalism.L2.Th1.F.Cm1.sqrt_mul_selfC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:45.977128+00:00
-- url     : https://prove2.me/submissions/bcb3bda2-6511-4841-862c-69c0f21b7344

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_sqrt_mul_self

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
open Formalism.L2.Th1.F.Cm1
namespace Formalism.L2.Th1.F.Cm1
theorem _root_.solution (d : ℕ) : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
  rw [← Complex.ofReal_mul, sqrt_mul_self, Complex.ofReal_natCast]
end Formalism.L2.Th1.F.Cm1

-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk4.hk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:32:56.33284+00:00
-- url     : https://prove2.me/submissions/554cdd43-11f6-470f-8f47-28d4f956d1ce

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EisensteinS2LimitFormulaOfHkLimit

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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk4
namespace Formalism.L2.Th1.F.Hk4
theorem _root_.solution (s : ℝ) (u w : ℂ) :
    hk s (u * w) = (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ) * hk s w := by
  unfold hk
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_pow, mul_inv]
  push_cast
  ring
end Formalism.L2.Th1.F.Hk4

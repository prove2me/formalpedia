-- Prove2me | solution 1 for Formalism.L2.Th1.F.Cm1.theta_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:03.145205+00:00
-- url     : https://prove2.me/submissions/2185c683-1afe-4900-9cf1-1ed93f7c4c76

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
namespace Cm1
private theorem cmTheta_eq_half_b_add_sqrt_half_I (b : ℤ) (d : ℕ) :
    Formalism.L2.Th1.F.cmTheta b d = (((b : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
  unfold Formalism.L2.Th1.F.cmTheta; push_cast; ring
private theorem re_ofReal_add_ofReal_mul_I (u v : ℝ) : ((u : ℂ) + (v : ℂ) * Complex.I).re = u := by simp
end Cm1
open Cm1
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Cm1
namespace Formalism.L2.Th1.F.Cm1
theorem _root_.solution (b : ℤ) (d : ℕ) : (cmTheta b d).re = (b : ℝ) / 2 := by
  rw [cmTheta_eq_half_b_add_sqrt_half_I, re_ofReal_add_ofReal_mul_I]
end Formalism.L2.Th1.F.Cm1

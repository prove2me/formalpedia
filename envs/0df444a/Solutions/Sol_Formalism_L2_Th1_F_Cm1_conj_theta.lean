-- Prove2me | solution 1 for Formalism.L2.Th1.F.Cm1.conj_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:02.046086+00:00
-- url     : https://prove2.me/submissions/748683f1-b0e7-4460-adf6-337c691d9d81

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
theorem _root_.solution (b : ℤ) (d : ℕ) :
    conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  rw [cmTheta_eq_half_b_add_sqrt_half_I]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring
end Formalism.L2.Th1.F.Cm1

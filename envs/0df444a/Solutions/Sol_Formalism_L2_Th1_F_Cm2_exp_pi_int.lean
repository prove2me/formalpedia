-- Prove2me | solution 1 for Formalism.L2.Th1.F.Cm2.exp_pi_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:37.981676+00:00
-- url     : https://prove2.me/submissions/1327f493-c786-4613-a408-651526556821

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_FormEvenIff

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
open Formalism.L2.Th1.F.Cm2
open Cm1
namespace Formalism.L2.Th1.F.Cm2
theorem _root_.solution (n : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (((n : ℤ) : ℝ) : ℂ)) = if Even n then 1 else -1 := by
  have e : (Real.pi : ℂ) * Complex.I * (((n : ℤ) : ℝ) : ℂ) = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.mp h).neg_one_zpow
end Formalism.L2.Th1.F.Cm2

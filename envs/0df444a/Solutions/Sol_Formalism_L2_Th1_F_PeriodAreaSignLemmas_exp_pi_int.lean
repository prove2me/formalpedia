-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodAreaSignLemmas.exp_pi_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:43.006491+00:00
-- url     : https://prove2.me/submissions/befdf61b-01e1-4ef9-96d1-277d928037d1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf

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
open PeriodAreaSignLemmas
open Formalism.L2.Th1.F.PeriodAreaSignLemmas
namespace Formalism.L2.Th1.F.PeriodAreaSignLemmas
theorem _root_.solution (k : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ)) = if Even k then 1 else -1 := by
  have : (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ) = (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.mp h).neg_one_zpow
end Formalism.L2.Th1.F.PeriodAreaSignLemmas

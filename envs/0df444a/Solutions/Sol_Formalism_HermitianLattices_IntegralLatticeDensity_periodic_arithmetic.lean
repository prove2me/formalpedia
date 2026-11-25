-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.periodic_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:04:51.880903+00:00
-- url     : https://prove2.me/submissions/839338f1-ce7c-43a6-a17e-47240bcf5f46

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : PerArithmetic := by
  unfold PerArithmetic
  intro d v γ Λ mη hd hv hm
  have hr : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hπ := Real.pi_pos
  have e1 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) hπ.ne', show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have e2 : Real.log (2 * Real.sqrt d) = Real.log 2 + Real.log (Real.sqrt d) :=
    Real.log_mul (by norm_num) hr.ne'
  have e3 : Real.log (2 * Real.pi / Real.sqrt d)
      = Real.log 2 + Real.log Real.pi - Real.log (Real.sqrt d) := by
    rw [Real.log_div (mul_pos two_pos hπ).ne' hr.ne', Real.log_mul (by norm_num) hπ.ne']
  have e4 : Real.log (2 * v / Real.sqrt d) = Real.log 2 + Real.log v - Real.log (Real.sqrt d) := by
    rw [Real.log_div (mul_pos two_pos hv).ne' hr.ne', Real.log_mul (by norm_num) hv.ne']
  have e5 : Real.log (Real.pi / v) = Real.log Real.pi - Real.log v := Real.log_div hπ.ne' hv.ne'
  refine ⟨?_, ?_⟩
  · rw [hm, e1, e2, e3]
    ring
  · rw [hm, e1, e2, e4, e5]
    ring
end Formalism.HermitianLattices.IntegralLatticeDensity

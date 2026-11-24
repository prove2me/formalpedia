-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures.integral_exp_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:58.048363+00:00
-- url     : https://prove2.me/submissions/8634f6f0-9a10-4f9c-addb-293c6eda0512

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_IntegralExpInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
namespace Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
theorem _root_.solution (k : ℤ) :
    ∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi), Complex.exp ((k : ℂ) * I * (θ : ℂ)) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  split_ifs with hk
  · subst hk; simp
  · have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((k : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I k]; congr 1; push_cast; ring
    rw [h1]; simp
end Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures

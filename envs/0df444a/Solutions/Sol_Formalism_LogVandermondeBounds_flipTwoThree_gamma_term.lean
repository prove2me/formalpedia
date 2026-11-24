-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.gamma_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:37:38.648483+00:00
-- url     : https://prove2.me/submissions/90e2159d-5afa-460d-b048-b6b6434d0b7b

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset MeasureTheory
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution (k : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-Real.pi * u)) (Set.Ioi 0) ∧
    ∫ u in Set.Ioi (0:ℝ), u ^ k * Real.exp (-Real.pi * u) = (k.factorial : ℝ) / Real.pi ^ (k+1) := by
  have hval : ∫ u in Set.Ioi (0:ℝ), u ^ k * Real.exp (-Real.pi * u)
      = (k.factorial : ℝ) / Real.pi ^ (k+1) := by
    have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k:ℝ) + 1) (r := Real.pi)
      (by positivity) Real.pi_pos
    have hc : ∫ u in Set.Ioi (0:ℝ), u ^ k * Real.exp (-Real.pi * u)
        = ∫ t in Set.Ioi (0:ℝ), t ^ ((k:ℝ) + 1 - 1) * Real.exp (-(Real.pi * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      simp only [add_sub_cancel_right, Real.rpow_natCast, neg_mul]
    rw [hc, key, Real.Gamma_nat_eq_factorial]
    rw [show ((k:ℝ) + 1) = ((k+1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [one_div, inv_pow]
    ring
  refine ⟨?_, hval⟩
  apply Integrable.of_integral_ne_zero
  rw [hval]
  have := Real.pi_pos
  positivity
end Formalism.LogVandermondeBounds.flipTwoThree

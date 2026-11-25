-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.sign_of_local_symbol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:04:58.737524+00:00
-- url     : https://prove2.me/submissions/d43f9fdb-be90-4a7c-a3bf-8680a990a3b5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Theorems.Thm_Formalism_HermitianLattices_IntegralLatticeDensity_power_of_unit_formula

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
theorem _root_.solution : SeSign := by
  unfold SeSign
  intro A _ q ε η hq h1 h2 n ζ e L
  have hηq : η ^ q = η := by
    obtain ⟨k, rfl⟩ := hq
    rw [pow_succ, pow_mul, sq, h2, one_pow, one_mul]
  have hε := power_of_unit_formula A q ε η h1 hηq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hηl : η ^ l * η ^ l = 1 := by rw [← mul_pow, h2, one_pow]
  rw [mul_pow, hε l, neg_pow]
  linear_combination ((-1) ^ l * ε * ζ (e - 2 * (l : ZMod n)) ^ q ^ l) * hηl
end Formalism.HermitianLattices.IntegralLatticeDensity

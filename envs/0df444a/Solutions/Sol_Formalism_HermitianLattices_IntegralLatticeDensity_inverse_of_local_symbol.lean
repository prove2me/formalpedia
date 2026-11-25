-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.inverse_of_local_symbol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:06:02.780817+00:00
-- url     : https://prove2.me/submissions/fc6b4aed-1dc7-498b-9076-49b2c2ca9d38

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
theorem _root_.solution : SeInverse := by
  unfold SeInverse
  intro A _ p _ _ n ζ e L
  haveI : ExpChar A p := ExpChar.prime (Fact.out)
  rw [show ∀ x : A, x ^ p ^ 2 = iterateFrobenius A p 2 x from
    fun x => by rw [iterateFrobenius_def]]
  rw [map_sum, Finset.sum_range_succ']
  simp only [map_mul, map_pow, map_neg, map_one, iterateFrobenius_def]
  have hidx : ∀ l : ℕ, e - 2 * ((l + 1 : ℕ) : ZMod n) = e - 2 - 2 * (l : ZMod n) := by
    intro l
    push_cast
    ring
  simp only [hidx]
  rw [add_right_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero (fun l _ => by ring)]
  simp
end Formalism.HermitianLattices.IntegralLatticeDensity

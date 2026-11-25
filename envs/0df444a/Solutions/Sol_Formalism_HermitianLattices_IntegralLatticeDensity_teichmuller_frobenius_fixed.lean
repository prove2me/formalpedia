-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.teichmuller_frobenius_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:08:57.384866+00:00
-- url     : https://prove2.me/submissions/2dad6a9f-3c85-4528-bea7-d6b96a523a93

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
theorem _root_.solution : TeichFrobenius := by
  unfold TeichFrobenius
  intro p _ k _ _ x s
  have key : ∀ y : k, WittVector.frobenius (WittVector.teichmuller p y)
      = WittVector.teichmuller p (y ^ p) := by
    intro y
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]
  suffices h : (WittVector.frobenius)^[s] (WittVector.teichmuller p x)
      = WittVector.teichmuller p (x ^ p ^ s) by
    rw [h, map_pow]
  induction s with
  | zero => simp
  | succ s ih => rw [Function.iterate_succ_apply', ih, key, ← pow_mul, ← pow_succ]
end Formalism.HermitianLattices.IntegralLatticeDensity

-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.uniformizer_logarithm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:47.211962+00:00
-- url     : https://prove2.me/submissions/a9c86ae6-8666-4fcb-98c1-36e42bd7298d

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
theorem _root_.solution : VarpiLog := by
  unfold VarpiLog
  intro R _ p q ϖ hq h
  have hϖq : ϖ ^ q = (p : R) * ϖ := by
    rw [← h, ← pow_succ]
    congr 1
    omega
  refine ⟨fun e => ?_, fun e he => ?_⟩
  · induction e with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih, mul_pow, hϖq, Finset.sum_range_succ', ← pow_mul]
      have hs : ∑ i ∈ range k, q ^ (i + 1) = q * ∑ i ∈ range k, q ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => pow_succ' q i)
      rw [hs]
      ring
  · induction e, he using Nat.le_induction with
    | base =>
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp only [pow_zero, pow_one]
      omega
    | succ k hk ih =>
      rw [Finset.sum_range_succ]
      have : 0 < q ^ k := pow_pos (by omega) k
      omega
end Formalism.HermitianLattices.IntegralLatticeDensity

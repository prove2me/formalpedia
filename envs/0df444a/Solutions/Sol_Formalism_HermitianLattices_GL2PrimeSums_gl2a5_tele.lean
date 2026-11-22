-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_tele
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:22.203145+00:00
-- url     : https://prove2.me/submissions/87eb0cb1-d3a7-4ba8-88bd-3ced0d0979ae

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution (g h : ℕ → ℝ) (K : ℕ) (hstep : ∀ n, K ≤ n → g (n + 1) ≤ h n - h (n + 1))
    (hh : ∀ n, 0 ≤ h n) (M : ℕ) : ∑ n ∈ Ioc K M, g n ≤ h K := by
  rcases Nat.lt_or_ge M K with hKM | hKM
  · rw [Finset.Ioc_eq_empty (by omega)]; simpa using hh K
  · have key : ∀ M, K ≤ M → ∑ n ∈ Ioc K M, g n ≤ h K - h M := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ M hM ih =>
        rw [Finset.sum_Ioc_succ_top hM]
        linarith [hstep M hM]
    linarith [key M hKM, hh M]
end Formalism.HermitianLattices.GL2PrimeSums

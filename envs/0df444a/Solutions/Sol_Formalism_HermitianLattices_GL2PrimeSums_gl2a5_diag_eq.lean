-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_diag_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:40.911189+00:00
-- url     : https://prove2.me/submissions/c269ca38-375c-4a59-b3c8-ca3a62789327

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_minFac_mem

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
theorem _root_.solution (x : ℝ) (N : ℕ) :
    ∑ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' *
      (if n.minFac = n'.minFac then (1 : ℝ) else 0) = ∑ p ∈ Icc 1 N, (primeTermWeight x N p) ^ 2 := by
  have h1 : ∀ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' *
      (if n.minFac = n'.minFac then (1 : ℝ) else 0) = cn x n * primeTermWeight x N n.minFac := by
    intro n _
    unfold primeTermWeight
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n' _
    by_cases h : n.minFac = n'.minFac
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]; ring
  rw [Finset.sum_congr rfl h1,
    ← Finset.sum_fiberwise_of_maps_to (fun n hn => gl2a5_minFac_mem hn)]
  apply Finset.sum_congr rfl; intro p _
  have h2 : ∀ n ∈ (primesLeFinset N).filter (fun n => n.minFac = p),
      cn x n * primeTermWeight x N n.minFac = cn x n * primeTermWeight x N p := by
    intro n hn
    rw [(mem_filter.1 hn).2]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, sq]
  rfl
end Formalism.HermitianLattices.GL2PrimeSums

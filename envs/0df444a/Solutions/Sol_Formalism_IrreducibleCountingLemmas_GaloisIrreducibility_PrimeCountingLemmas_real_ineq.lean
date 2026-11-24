-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.real_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:20.901853+00:00
-- url     : https://prove2.me/submissions/621b8574-9e18-4ae2-89f2-f5b1a0c8817c

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Nat
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
theorem _root_.solution {y l L k : ℝ} (hy : 141 ≤ y) (hl1 : 0.6931471803 < l) (hl2 : l < 0.6931471808)
    (hL : L ≤ 2 * (7 * l + y / 128 - 1))
    (h : y ^ 2 * l / 3 < (y / 3 + 4 + k) * L) : y ^ 2 + 1 ≤ 5 * (k - 3) * L := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  rcases le_or_gt L 0 with hL0 | hL0
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y / 3 + 7) (neg_nonneg.2 hL0),
      mul_le_mul_of_nonneg_left hl1.le (sq_nonneg y), mul_nonneg (by linarith : (0 : ℝ) ≤ y - 141) hy0]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y / 3 + 7) (by linarith : (0 : ℝ) ≤ 2 * (7 * l + y / 128 - 1) - L),
      mul_le_mul_of_nonneg_left hl1.le (sq_nonneg y), mul_nonneg (by linarith : (0 : ℝ) ≤ y - 141) hy0,
      mul_le_mul_of_nonneg_left hl2.le hy0]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas

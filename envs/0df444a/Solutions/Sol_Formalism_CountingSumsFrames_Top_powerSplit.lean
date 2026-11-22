-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.powerSplit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:43.534688+00:00
-- url     : https://prove2.me/submissions/f237bc88-613c-494e-a8fe-7b32c1a6c0c8

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.PowerSplit := by
  intro R _ D h π P n c hP
  rw [add_pow]
  refine Ideal.sum_mem _ fun j hj => ?_
  by_cases hc : c ≤ n - j
  · apply Ideal.mem_sup_right
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_left
    rw [mul_pow]
    apply Ideal.mul_mem_right
    exact Ideal.mem_span_singleton.mpr (pow_dvd_pow π hc)
  · apply Ideal.mem_sup_left
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_right
    rw [Ideal.mem_span_singleton, ← pow_mul]
    have hjP : j ≤ P * j := Nat.le_mul_of_pos_left j hP
    exact pow_dvd_pow D (by omega)
end Formalism.CountingSumsFrames.Top

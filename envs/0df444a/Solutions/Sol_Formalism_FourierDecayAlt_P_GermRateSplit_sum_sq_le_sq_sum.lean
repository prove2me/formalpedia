-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermRateSplit.sum_sq_le_sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:01:05.738266+00:00
-- url     : https://prove2.me/submissions/7599f45a-aea9-4552-9cf3-f64de120c0ab

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermRateSplit
open Finset
open scoped ComplexConjugate InnerProductSpace
namespace Formalism.FourierDecayAlt.P.GermRateSplit
theorem _root_.solution {I : Type} [Fintype I] (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 2 ≤ (∑ i, x i) ^ 2 := by
  rw [sq, sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => hx j) (mem_univ i)) (hx i)
end Formalism.FourierDecayAlt.P.GermRateSplit

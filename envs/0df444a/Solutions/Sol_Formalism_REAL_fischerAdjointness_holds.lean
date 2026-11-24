-- Prove2me | solution 1 for Formalism.REAL.fischerAdjointness_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:46:36.492611+00:00
-- url     : https://prove2.me/submissions/cf0d102a-a9b1-4f17-a1cc-20dd213d0ff1

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Theorems.Thm_Formalism_REAL_fischerInner_sum_left
import Theorems.Thm_Formalism_REAL_fischerInner_sum_right
import Theorems.Thm_Formalism_REAL_fischerInner_neg_left
import Theorems.Thm_Formalism_REAL_fischerInner_neg_right
import Theorems.Thm_Formalism_REAL_fischerInner_oscillatorLower
import Theorems.Thm_Formalism_REAL_fischerInner_oscillatorRaise
import Theorems.Thm_Formalism_REAL_signMatch_mul_left
import Theorems.Thm_Formalism_REAL_signMatch_mul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {M n' : ℕ}
namespace Formalism.REAL
theorem _root_.solution : FockAdj := by
  intro M n' ε ε' f g
  refine ⟨fun i a => fischerInner_oscillatorLower ε ε' i a f g, fun i j => ?_, fun a b => ?_⟩
  · simp only [Eg, LinearMap.sum_apply, Module.End.mul_apply, fischerInner_sum_left,
      fischerInner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [fischerInner_oscillatorRaise, fischerInner_oscillatorLower, ← mul_assoc, signMatch_mul_left]
  · simp only [Eg', LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
      fischerInner_neg_left, fischerInner_neg_right, fischerInner_sum_left, fischerInner_sum_right, mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fischerInner_oscillatorRaise, fischerInner_oscillatorLower, ← mul_assoc, signMatch_mul_right]
end Formalism.REAL

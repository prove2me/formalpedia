-- Prove2me | solution 1 for Formalism.LT.TorsProof.eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:45.014518+00:00
-- url     : https://prove2.me/submissions/9168c8b9-6308-4005-be40-5910905a69f4

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.LT Formalism.LT.TorsProof
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {π : K} {q : ℕ} {e : Polynomial K}
namespace Formalism.LT.TorsProof
theorem _root_.solution (e : Polynomial K) (x : K) :
    e.eval x = ∑ i ∈ Finset.range (e.natDegree + 1), e.coeff i * x ^ i :=
  Polynomial.eval_eq_sum_range x
end Formalism.LT.TorsProof

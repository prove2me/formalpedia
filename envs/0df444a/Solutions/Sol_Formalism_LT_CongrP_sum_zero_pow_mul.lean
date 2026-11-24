-- Prove2me | solution 1 for Formalism.LT.CongrP.sum_zero_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:55.258013+00:00
-- url     : https://prove2.me/submissions/8bddb90b-b9ae-452d-ba8a-79b3b0356f8b

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {R : Type*} [CommRing R]
namespace Formalism.LT.CongrP
theorem _root_.solution (n : ℕ) :
    ∑ i ∈ Finset.range n, (0 : R) ^ i * (0 : R) ^ (n - 1 - i) = if n = 1 then 1 else 0 := by
  rcases n with _ | n
  · simp
  · rw [Finset.sum_range_succ']
    simp only [pow_succ, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, pow_zero, one_mul]
    rcases n with _ | n <;> simp
end Formalism.LT.CongrP

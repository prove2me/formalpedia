-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.coeff_sum_C_mul_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:32.409267+00:00
-- url     : https://prove2.me/submissions/887b9bd0-4c66-4f20-8b83-1f9f14773328

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}
namespace Formalism.BaseCaseIdentities
theorem _root_.solution [Fintype Z] [DecidableEq Z] (y : Z → k) (M : ℕ) (B : Z →₀ ℕ) :
    coeff B (∑ d, C (y d) * X d ^ M : MvPowerSeries Z k)
      = ∑ d, if B = Finsupp.single d M then y d else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp
end Formalism.BaseCaseIdentities

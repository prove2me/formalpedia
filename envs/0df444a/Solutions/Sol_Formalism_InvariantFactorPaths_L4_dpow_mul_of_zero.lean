-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.dpow_mul_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:18:41.686406+00:00
-- url     : https://prove2.me/submissions/d076a393-8480-4238-9a37-8576d909b0bd

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_succ_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (c : Fin r) (x g : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : glAct p LL j 0 c x = 0) (k : ℕ) :
    dpow p LL j c k (x * g) = x * dpow p LL j c k g := by
  cases k with
  | zero => rw [dpow_zero, dpow_zero]
  | succ k => rw [dpow_succ_mul p LL j c x g (by rw [hx, map_zero]) k, hx, zero_mul, add_zero]
end Formalism.InvariantFactorPaths.L4

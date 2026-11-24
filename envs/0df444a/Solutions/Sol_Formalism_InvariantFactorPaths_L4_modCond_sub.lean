-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.modCond_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:56:43.489849+00:00
-- url     : https://prove2.me/submissions/7e63fd31-47d4-45c1-bac6-a93f629f78dc

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_add
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_neg

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
variable (M : WithTop ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (f g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : ModCond p LL j M f)
    (hg : ModCond p LL j M g) : ModCond p LL j M (f - g) := by
  rw [sub_eq_add_neg]
  exact modCond_add p LL j M _ _ hf (modCond_neg p LL j M _ hg)
end Formalism.InvariantFactorPaths.L4

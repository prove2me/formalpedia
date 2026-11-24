-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.modCond_last_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:28:33.885714+00:00
-- url     : https://prove2.me/submissions/05152326-0edf-4c75-b3e7-9271899d4877

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_mul_of_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_of_stable
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_small
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_dpow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_wt
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_withTop_shift


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
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true)
    (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hg : ModCond p LL j M (X (Fin.last K, (0 : Fin r)) * g)) :
    ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g := by
  refine modCond_of_stable p LL j _ {g | ModCond p LL j M (X (Fin.last K, (0 : Fin r)) * g)} ?_ ?_ g hg
  · intro x hx a ha k
    show ModCond p LL j M _
    rw [← dpow_mul_of_zero p LL j a _ _ (by rw [last_X p LL j hj hv, if_neg ha]) k]
    exact modCond_dpow p LL j M _ hx a ha k
  · intro x hx m hm
    have := modCond_small p LL j M _ hx (Finsupp.single (Fin.last K, (0 : Fin r)) 1 + m)
      (by rw [last_wt LL j hj hv, if_pos rfl, withTop_shift]; exact hm)
    rwa [coeff_X_mul] at this
end Formalism.InvariantFactorPaths.L4

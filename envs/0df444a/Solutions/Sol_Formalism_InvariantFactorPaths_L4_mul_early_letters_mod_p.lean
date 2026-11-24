-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mul_early_letters_mod_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:28:38.014769+00:00
-- url     : https://prove2.me/submissions/85e41d51-3a55-4fd9-9d84-bd566b673baf

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_mul_of_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_of_stable
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_small
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_dpow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_single_add


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
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : MulEarlyModP := by
  intro p _ K r _ LL j M c h hj hh
  have hlt : ¬ ((Fin.last K : Fin (K + 1)) : ℕ) < j := by rw [Fin.val_last]; omega
  refine modCond_of_stable p LL j M {g | ModCond p LL j M (X (Fin.last K, c) * g)} ?_ ?_ h hh
  · intro x hx a ha k
    show ModCond p LL j M _
    rw [← dpow_mul_of_zero p LL j a _ _ (by rw [glAct_X, if_neg hlt]) k]
    exact modCond_dpow p LL j M _ hx a ha k
  · intro x hx m hm
    have := modCond_small p LL j M _ hx (Finsupp.single (Fin.last K, c) 1 + m)
      (by rw [wt_single_add, if_neg hlt, zero_mul, add_zero]; exact hm)
    rwa [coeff_X_mul] at this
end Formalism.InvariantFactorPaths.L4

-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.raising_degree_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:46.671693+00:00
-- url     : https://prove2.me/submissions/005e8f6d-38a7-41fa-820e-13d6befeda56

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_X_mul_pol
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
import Theorems.Thm_Formalism_CountingSumsFrames_pol_iff_eul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_setLast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : UDeg := by
  intro p _ K r LL c Cs a o F hF
  rw [Uop_apply]
  refine Submodule.sub_mem _ (X_mul_pol LL a o _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hF) ?_))
    (Submodule.sum_mem _ fun b _ => X_mul_pol LL b o _ ?_)
  · rw [(pol_iff_eul _ F).mp hF (Fin.last K)]
    exact Submodule.smul_mem _ _ hF
  · have := glAct_pol (setLast LL o) K a b F hF
    rwa [glAct_setLast] at this
end Formalism.InvariantFactorPaths.L4

-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eW_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:49.778308+00:00
-- url     : https://prove2.me/submissions/46026987-b6cf-487c-aebf-951aa2e8f727

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_mem
import Theorems.Thm_Formalism_GM_FockB_mulLeftX_mem
import Theorems.Thm_Formalism_GM_FockB_ops_commute
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_disj_last
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_mem


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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (s t a b : Fin r) :
    Commute (glAct p LL K a b : Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) (eW p K s t) := by
  refine (FockB.ops_commute disj_last ?_ (glAct_mem LL K a b)).symm
  unfold eW
  rw [← Module.End.mul_eq_comp]
  exact mul_mem (FockB.mulLeftX_mem (last_mem s)) (FockB.pderiv_mem (last_mem t))
end Formalism.InvariantFactorPaths.L4

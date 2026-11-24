-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pderiv_ycond_early
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:48.454507+00:00
-- url     : https://prove2.me/submissions/166e7983-7a00-4175-afc5-f7764cc2044a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ops_ycond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (hj : j ≤ K) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ x ∈ YCond p LL j Mt, pderiv (Fin.last K, c) x ∈ YCond p LL j Mt :=
  ops_ycond LL j Mt (pderiv (Fin.last K, c)).toLinearMap (FockB.pderiv_mem (by
    simp only [Set.mem_ofPred_eq, Fin.val_last]; exact hj))
end Formalism.InvariantFactorPaths.L4

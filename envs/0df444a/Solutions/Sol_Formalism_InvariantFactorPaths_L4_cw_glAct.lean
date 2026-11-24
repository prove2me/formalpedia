-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.cw_glAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:45:56.760852+00:00
-- url     : https://prove2.me/submissions/23e48cc3-7564-4ebe-a605-9cb56aa62f5d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_compL_intertwine
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wp_early
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_keep
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
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
theorem _root_.solution (LL : Letters (K + 1)) (γ : Fin r → ℤ) (s t : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    cw p K γ (glAct p LL K s t x) = glAct p LL K s t (cw p K γ x) := by
  refine compL_intertwine (glAct p LL K s t) _ _ ?_ ?_ x
  · refine glAct_keep LL K s t _ _ ?_ ?_
    · intro i hi _ m hm _
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [wp_early i hi]; exact hm
    · intro i hi _ m hm _
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [wp_early i hi]; exact hm
  · refine glAct_keep LL K s t _ _ ?_ ?_
    · intro i hi _ m hm _
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [wp_early i hi]; exact hm
    · intro i hi _ m hm _
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [wp_early i hi]; exact hm
end Formalism.InvariantFactorPaths.L4

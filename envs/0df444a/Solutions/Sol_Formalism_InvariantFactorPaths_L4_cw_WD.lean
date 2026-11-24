-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.cw_WD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:58:10.723131+00:00
-- url     : https://prove2.me/submissions/db57bddc-761a-43f5-b8c0-12b3bbd2e37d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_compL_intertwine
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wp_last
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_shiftW_iff
import Theorems.Thm_Formalism_CountingSumsFrames_XD_keep
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
theorem _root_.solution (γ : Fin r → ℤ) (s t : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    cw p K γ (X (Fin.last K, s) * pderiv (Fin.last K, t) x) =
      X (Fin.last K, s) * pderiv (Fin.last K, t) (cw p K (shiftW γ t s) x) := by
  refine compL_intertwine
    ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, s))) ∘ₗ (pderiv (Fin.last K, t)).toLinearMap) _ _ ?_ ?_ x
  · refine XD_keep _ _ _ _ ?_
    intro m hm hb
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [wp_last s t m hb, shiftW_iff]; exact hm
  · refine XD_keep _ _ _ _ ?_
    intro m hm hb
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [wp_last s t m hb, shiftW_iff]; exact hm
end Formalism.InvariantFactorPaths.L4

-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glAct_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:36.710549+00:00
-- url     : https://prove2.me/submissions/a27b6b75-3b4d-408b-8786-5a30f4d971a7

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
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
theorem _root_.solution {N : ℕ} (LL : Letters N) (j : ℕ) (s t : Fin r) (v : Fin N × Fin r) (hs : s ≠ v.2) (ht : t ≠ v.2) :
    ∀ z ∈ FreeOf p v, glAct p LL j s t z ∈ FreeOf p v := by
  refine glAct_keep LL j s t _ _ ?_ ?_
  · intro i _ _ m hm _
    simp only [Set.mem_ofPred_eq] at hm ⊢
    have : ((i, s) : Fin N × Fin r) ≠ v := fun h => hs (by rw [← h])
    simp [Finsupp.single_apply, this, hm]
  · intro i _ _ m hm _
    simp only [Set.mem_ofPred_eq] at hm ⊢
    have : ((i, t) : Fin N × Fin r) ≠ v := fun h => ht (by rw [← h])
    simp [Finsupp.single_apply, this, hm]
end Formalism.InvariantFactorPaths.L4

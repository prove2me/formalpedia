-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glAct_succ_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:49:19.167388+00:00
-- url     : https://prove2.me/submissions/275f6f96-230a-4a95-9ec8-26846f45175c

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_comm
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_split
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glRest_comm
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
theorem _root_.solution (LL : Letters (K + 1)) (s t a b : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL (K + 1) s t (glAct p LL K a b F) - glAct p LL K a b (glAct p LL (K + 1) s t F) =
      (if t = a then glAct p LL K s b F else 0) - (if b = s then glAct p LL K a t F else 0) := by
  rw [glAct_split LL K (K + 1) s t]
  simp only [LinearMap.add_apply, map_add]
  rw [glRest_comm LL K (K + 1) (Nat.le_succ K) s t a b F, ← glAct_comm LL K s t a b F]
  abel
end Formalism.InvariantFactorPaths.L4

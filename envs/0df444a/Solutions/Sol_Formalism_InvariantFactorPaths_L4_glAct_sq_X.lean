-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glAct_sq_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:02.593777+00:00
-- url     : https://prove2.me/submissions/a627e278-91f7-43d2-9a31-f92bb8dff5cc

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_X


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
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (c : Fin r) (hc : c ≠ 0) (v : Fin N × Fin r) :
    glAct p LL j 0 c (glAct p LL j 0 c (X v)) = 0 := by
  obtain ⟨i, c'⟩ := v
  rw [glAct_X]
  split_ifs with h1 h2 h3 h3
  · rw [glAct_X, if_pos h1, if_pos h2, if_neg hc]
  · exact map_zero _
  · rw [map_neg, glAct_X, if_pos h1, if_neg h2, if_neg (Ne.symm hc), neg_zero]
  · exact map_zero _
  · exact map_zero _
end Formalism.InvariantFactorPaths.L4

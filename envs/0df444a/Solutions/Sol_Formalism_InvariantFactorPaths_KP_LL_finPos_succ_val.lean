-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.finPos_succ_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:48.516744+00:00
-- url     : https://prove2.me/submissions/de292d66-6778-4a62-be6f-f9a30be7b717

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_SmulMemOfNorm
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pos_succ_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
variable {N r : ℕ} (D : BlockData N)
variable {D}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hB : D.BlockOK) (i : Fin D.T.t) :
    (finPos N (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  show min (D.T.pos i + 1) N = D.T.pos i + 1
  omega
end Formalism.InvariantFactorPaths.KP.LL

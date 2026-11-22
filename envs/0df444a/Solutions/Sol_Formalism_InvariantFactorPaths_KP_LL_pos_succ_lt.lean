-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.pos_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:37.231599+00:00
-- url     : https://prove2.me/submissions/a07fb7fa-4b83-4176-a8ce-eda05b5c1b8e

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_SmulMemOfNorm
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal

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
theorem _root_.solution (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 + 1 < N := by
  obtain ⟨_, h2, _, h4⟩ := hB
  have := h2 i
  omega
end Formalism.InvariantFactorPaths.KP.LL

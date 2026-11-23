-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.wv_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:31.560023+00:00
-- url     : https://prove2.me/submissions/d393f732-9000-4c4b-9110-a2b02a94aa08

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_finPos_pos_val
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_letterAt_pos_val


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
open scoped Pointwise
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
variable {p D}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hB : D.BlockOK) (i : Fin D.T.t) (c : Fin r) :
    wv D i c = chainEmb N r D.T.t (D.letterAt (D.T.pos i), c) := by
  simp only [wv, chainEmb, Sum.inl.injEq, Prod.mk.injEq, and_true]
  apply Fin.ext
  rw [finPos_pos_val hB, Fin.coe_castSucc, letterAt_pos_val hB]
end Formalism.InvariantFactorPaths.KP.LL

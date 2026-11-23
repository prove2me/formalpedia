-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.ev_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:11.308655+00:00
-- url     : https://prove2.me/submissions/15a55b74-e0e9-4184-8e30-a28072edf783

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_finPos_succ_val
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_letterAt_succ_val


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
    ev D i c = chainEmb N r D.T.t (D.letterAt (D.T.pos i + 1), c) := by
  simp only [ev, chainEmb, Sum.inl.injEq, Prod.mk.injEq, and_true]
  apply Fin.ext
  rw [finPos_succ_val hB, Fin.coe_castSucc, letterAt_succ_val hB]
end Formalism.InvariantFactorPaths.KP.LL

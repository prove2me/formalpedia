-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.ev_ne_xi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:41:54.559943+00:00
-- url     : https://prove2.me/submissions/b1c3ad2e-1637-49e6-a2dc-fe62522799f4

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_BiHomPlus
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_finPos_succ_val
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : ev D i c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [ev, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  have h1 := congrArg Fin.val h.1
  rw [finPos_succ_val hB, Fin.val_last] at h1
  have := pos_succ_lt hB i
  omega
end Formalism.InvariantFactorPaths.KP.LL

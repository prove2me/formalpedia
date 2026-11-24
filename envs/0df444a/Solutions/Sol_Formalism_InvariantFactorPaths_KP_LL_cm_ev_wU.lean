-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_ev_wU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:04.976127+00:00
-- url     : https://prove2.me/submissions/53f8e919-91d5-4e95-bc9f-0a24e50c60e1

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_finPos_succ_val
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pos_lt_u


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
theorem _root_.solution (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : ev D i d ≠ wU D c := by
  intro h'
  simp only [ev, wU, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_succ_val hB, Fin.val_castSucc] at this
  have := pos_lt_u hB i
  omega
end Formalism.InvariantFactorPaths.KP.LL

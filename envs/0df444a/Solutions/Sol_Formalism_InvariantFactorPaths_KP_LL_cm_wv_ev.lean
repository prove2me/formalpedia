-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_wv_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:47.410967+00:00
-- url     : https://prove2.me/submissions/fc710d81-58e4-4541-a0af-19c971349056

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_finPos_pos_val
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_finPos_succ_val
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pos_ne_succ


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
theorem _root_.solution (hB : D.BlockOK) (i k : Fin D.T.t) (c d : Fin r) : wv D i d ≠ ev D k c := by
  intro h'
  simp only [wv, ev, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_pos_val hB, finPos_succ_val hB] at this
  exact pos_ne_succ hB i k this
end Formalism.InvariantFactorPaths.KP.LL
